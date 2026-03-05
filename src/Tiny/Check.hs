module Tiny.Check
  ( M,
    check,
    infer,
    inferProgram,
    withEmptyCtx,
    withGlobals,
  )
where

import Control.Monad (unless)
import Text.Megaparsec (SourcePos)

import Tiny.Core
import Tiny.Env
import Tiny.Syntax
import Tiny.Value
import Tiny.Renaming

type M = Either (String, SourcePos)

data Locals
  = LocalsEmpty
  | LocalsVal Name VTy Locals
  | LocalsLock Locals

type CheckArgs v = (FreshArg, EnvArg v, ?locals :: Locals, ?globals :: Globals, ?pos :: SourcePos)

withEmptyCtx :: SourcePos -> (CheckArgs v => a) -> a
withEmptyCtx pos a =
  let ?fresh = 0
      ?env = emptyEnv
      ?locals = LocalsEmpty
      ?globals = Globals []
      ?pos = pos
   in a

withGlobals :: Globals -> (CheckArgs v => a) -> (CheckArgs v => a)
withGlobals gs a = let ?globals = gs in a

ctxDefine :: Name -> v -> VTy -> (CheckArgs v => a) -> (CheckArgs v => a)
ctxDefine x v ty act = define v $ let ?locals = LocalsVal x ty ?locals in act

ctxDefineGlobal :: Name -> Val -> VTy -> (CheckArgs Val => a) -> (CheckArgs Val => a)
ctxDefineGlobal x v ty act = let ?globals = Globals ((x, (v, ty)) : globalNames ?globals) in act

ctxDefineUnit :: Lvl -> (CheckArgs Val => a) -> (CheckArgs Val => a)
ctxDefineUnit lvl act = defineUnit lvl $ let ?locals = LocalsLock ?locals in act

ctxDefineStuck :: Keyable v => (CheckArgs v => a) -> (CheckArgs v => a)
ctxDefineStuck act = defineStuck $ let ?locals = LocalsLock ?locals in act

ctxDefineNextVar :: Name -> VTy -> (CheckArgs Val => Val -> a) -> (CheckArgs Val => a)
ctxDefineNextVar x ty act = defineNextVar let ?locals = LocalsVal x ty ?locals in act

report :: (?pos :: SourcePos) => String -> M a
report msg = Left (msg, ?pos)

findLocal :: CheckArgs Val => Name -> [Raw] -> M (Maybe (Tm, VTy))
findLocal x rkeys = go 0 (envVars ?env) ?locals rkeys
  where
    go _ EnvEmpty LocalsEmpty _ = pure Nothing
    go i (EnvVal _ env') (LocalsVal x' ty locals') keys
      | x == x' = case keys of
          [] -> do
            keyst <- mapM (\key -> check key VTiny) rkeys
            pure (Just (Var i keyst, ty))
          _ -> report ("too many keys provided: " ++ x)
      | otherwise = go (i + 1) env' locals' keys
    go _ (EnvLock _) (LocalsLock _) [] = report ("not enough keys provided: " ++ x)
    go i (EnvLock fenv) (LocalsLock locals') (key : keys) = do
      keyt <- check key VTiny
      let keyv = eval keyt
      go (i + 1) (fenv keyv) locals' keys
    go _ _ _ _ = error "impossible"

-- TODO: error on keys
findGlobal :: CheckArgs Val => Name -> [Raw] -> M (Maybe (Tm, VTy))
findGlobal x rkeys = do
  case lookup x (globalNames ?globals) of
    Just (_, vty) -> pure (Just (GlobalVar x, vty))
    Nothing -> pure Nothing

check :: CheckArgs Val => Raw -> VTy -> M Tm
check t a = case (t, a) of
  (RSrcPos pos t', a') ->
    let ?pos = pos
     in check t' a'
  (RLet x ty t' u, a') -> do
    ty' <- check ty VU
    let vty = eval ty'
    t'' <- check t' vty
    let vt = eval t''
    u' <- ctxDefine x vt vty $ check u a'
    pure (Let x ty' t'' u')
  (RLam x t', VPi _ a' b) ->
    Lam x <$> ctxDefineNextVar x a' (\var -> check t' (b ∙ var))
  (RPair a1 b1, VSg _ aty bty) -> do
    a' <- check a1 aty
    b' <- check b1 (bty ∙ eval a')
    pure (Pair a' b')
  (RRootIntro t', VRoot a') ->
    RootIntro <$> ctxDefineStuck (check t' (coapplyStuck a'))
  (RLam x t', VPath _ c a0 a1) -> do
    t'' <- ctxDefineNextVar x VTiny (\var -> check t' (c ∙ var))
    unless
      ( eq a0 (define VTiny0 (eval t''))
          && eq a1 (define VTiny1 (eval t''))
      )
      (report "endpoint mismatch: ")
    pure $ PLam x t'' (quote a0) (quote a1)
  _ -> do
    (t', tty) <- infer t
    unless (eq tty a) $ report ("type mismatch: " ++ show tty ++ ", " ++ show a)
    pure t'

infer :: CheckArgs Val => Raw -> M (Tm, VTy)
infer r = case r of
  RSrcPos pos t ->
    let ?pos = pos
     in infer t
  RU -> pure (U, VU)
  RLet x a t u -> do
    a' <- check a VU
    let va = eval a'
    t' <- check t va
    let vt = eval t'
    (u', uty) <- ctxDefine x vt va $ infer u
    pure (Let x a' t' u', uty)
  RPi x a b -> do
    a' <- check a VU
    b' <- ctxDefineNextVar x (eval a') (\_ -> check b VU)
    pure (Pi x a' b', VU)
  RApp t u -> do
    (t', tty) <- infer t
    case tty of
      VPi _ a' b -> do
        u' <- check u a'
        pure (App t' u', b ∙ eval u')
      _ ->
        report "Expected a function type"
  RLam {} -> report "Can't infer type for lambda expression"
  RSg x a b -> do
    a' <- check a VU
    b' <- ctxDefineNextVar x (eval a') (\_ -> check b VU)
    pure (Sg x a' b', VU)
  RPair {} -> report "Can't infer type for pair"
  RFst p -> do
    (t, ty) <- infer p
    case ty of
      VSg _ a' _ -> pure (Fst t, a')
      _ -> report "expected Sg type"
  RSnd p -> do
    (t, ty) <- infer p
    case ty of
      VSg _ _ b -> pure (Snd t, b ∙ eval (Fst t))
      _ -> report "expected Sg type"
  RVar x rkeys -> do
    local <- findLocal x rkeys
    case local of
      Just (tm, ty) -> pure (tm, ty)
      Nothing -> do
        global <- findGlobal x rkeys
        case global of
          Just (tm, ty) -> pure (tm, ty)
          Nothing -> report ("variable out of scope: " ++ x)
  RTiny -> pure (Tiny, VU)
  RRoot a -> do
    a' <- ctxDefineStuck $ check a VU
    pure (Root a', VU)
  RRootElim x t -> do
    (t', tty) <- ctxDefineNextVar x VTiny (\_ -> infer t)
    case tty of
      VRoot c -> pure (RootElim x t', coapply c (Lvl $ envLength ?env))
      _ -> report "Expected a root type"
  RRootIntro {} -> report "Can't infer type for rintro expression"
  RTiny0 -> pure (Tiny0, VTiny)
  RTiny1 -> pure (Tiny1, VTiny)
  RPath a0 a1 -> do
    (a0', aty) <- infer a0
    a1' <- check a1 aty
    pure (Path "_" (ctxDefineNextVar "_" VTiny (\_ -> quote aty)) a0' a1', VU)

checkOrInfer :: CheckArgs Val => Raw -> Maybe Raw -> M (Tm, Ty)
checkOrInfer t Nothing = do
  (tm, vty) <- infer t
  pure (tm, quote vty)
checkOrInfer t (Just rawA) = do
  atm <- check rawA VU
  let a = eval atm
  body <- check t a
  pure (body, atm)

withArgs :: CheckArgs Val => ([RawArg] -> (CheckArgs Val => M (Tm, Ty)) -> M (Tm, Ty))
withArgs [] action = action
withArgs ((RawArg x a_n) : args) action = do
  a <- check a_n VU
  ctxDefineNextVar x (eval a) $ \_ -> do
    (t, b) <- withArgs args action
    pure (Lam x t, Pi x a b)

inferTopDef :: CheckArgs Val => [RawArg] -> Maybe Raw -> Raw -> M (Tm, VTy)
inferTopDef args mret rhs = do
  (body, retty) <- withArgs args $ checkOrInfer rhs mret
  pure (body, eval retty)

inferTopDefs :: CheckArgs Val => [RawDecl] -> M Globals
inferTopDefs [] = pure ?globals
inferTopDefs ((RTopDef pos x args mty rhs) : rest) = let ?pos = pos in do
  (t, a) <- inferTopDef args mty rhs
  let v = eval t
  ctxDefineGlobal x v a (inferTopDefs rest)

inferProgram :: CheckArgs Val => RawProgram -> M (Globals, Maybe (Tm, Ty))
inferProgram (RProgram defs mt) = do
  globals <- inferTopDefs defs
  case mt of
    Nothing -> pure (globals, Nothing)
    Just a  -> withGlobals globals $ do
      (t, vty) <- infer a
      pure (globals, Just (t, quote vty))
