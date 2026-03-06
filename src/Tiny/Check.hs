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
      ?globals = Globals [] [] []
      ?pos = pos
   in a

withGlobals :: Globals -> (CheckArgs v => a) -> (CheckArgs v => a)
withGlobals gs a = let ?globals = gs in a

ctxDefine :: Name -> v -> VTy -> (CheckArgs v => a) -> (CheckArgs v => a)
ctxDefine x v ty act = define v $ let ?locals = LocalsVal x ty ?locals in act

ctxDefineGlobal :: Name -> Val -> VTy -> (CheckArgs Val => a) -> (CheckArgs Val => a)
ctxDefineGlobal x v ty act =
  let gs = ?globals
   in let ?globals = gs {globalNames = (x, (v, ty)) : globalNames gs}
       in act

ctxDefineTyConInfo :: TyConInfo -> (CheckArgs Val => a) -> (CheckArgs Val => a)
ctxDefineTyConInfo tc act =
  let gs = ?globals
   in let ?globals = gs {globalTyCons = (tyConName tc, tc) : globalTyCons gs}
       in act

ctxDefineConInfo :: ConInfo -> (CheckArgs Val => a) -> (CheckArgs Val => a)
ctxDefineConInfo ci act =
  let gs = ?globals
   in let ?globals = gs {globalCons = (conName ci, ci) : globalCons gs}
       in act

ctxDefineUnit :: Lvl -> (CheckArgs Val => a) -> (CheckArgs Val => a)
ctxDefineUnit lvl act = defineUnit lvl $ let ?locals = LocalsLock ?locals in act

ctxDefineStuck :: Keyable v => (CheckArgs v => a) -> (CheckArgs v => a)
ctxDefineStuck act = defineStuck $ let ?locals = LocalsLock ?locals in act

ctxDefineNextVar :: Name -> VTy -> (CheckArgs Val => Val -> a) -> (CheckArgs Val => a)
ctxDefineNextVar x ty act =
  let ?locals = LocalsVal x ty ?locals
   in defineNextVar act

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
findGlobalMaybe :: CheckArgs Val => Name -> Maybe (Tm, VTy)
findGlobalMaybe x =
  case lookup x (globalNames ?globals) of
    Just (_, vty) -> Just (GlobalVar x, vty)
    Nothing -> Nothing

findGlobal :: CheckArgs Val => Name -> M (Tm, VTy)
findGlobal x = do
  case findGlobalMaybe x of
    Just r -> pure r
    Nothing -> report ("unknown global: " ++ x)

findConInfo :: CheckArgs v => Name -> M ConInfo
findConInfo x =
  case lookup x (globalCons ?globals) of
    Just ci -> pure ci
    Nothing -> report ("unknown constructor: " ++ x)

data TelArg = TelArg Name Ty

withRawArgs :: CheckArgs Val => [RawArg] -> (CheckArgs Val => [TelArg] -> M a) -> M a
withRawArgs = go []
  where
    go :: CheckArgs Val => [TelArg] -> [RawArg] -> (CheckArgs Val => [TelArg] -> M a) -> M a
    go rev [] k = k (reverse rev)
    go rev (RawArg x rawA : rest) k = do
      a <- check rawA VU
      let va = eval a
      ctxDefineNextVar x va $ \_ ->
        go (TelArg x a : rev) rest k

wrapPis :: [TelArg] -> Ty -> Ty
wrapPis infos body = foldr (\(TelArg x a) b -> Pi x a b) body infos

expectTyCon :: CheckArgs v => VTy -> M (TyConInfo, [Val])
expectTyCon = \case
  VTyCon tc params -> pure (tc, params)
  t -> report ("expected an inductive type, got " ++ show t)

instantiateTyCon :: CheckArgs Val => ConInfo -> [Val] -> M VTy
instantiateTyCon ci params = do
  (_, cty) <- findGlobal (conName ci)
  go cty params
  where
    go ty [] = pure ty
    go (VPi _ _ b) (u : us) = go (b ∙ u) us
    go ty _ = report ("not enough parameters for " ++ conName ci ++ ": " ++ show ty)

orderedConInfos :: CheckArgs v => TyConInfo -> M [ConInfo]
orderedConInfos tc = mapM findConInfo (tyConConstructors tc)

withConFields ::
  CheckArgs Val =>
  Name ->
  VTy ->
  [Name] ->
  (CheckArgs Val => [Val] -> M a) ->
  M a
withConFields cname = go []
  where
    go :: CheckArgs Val => [Val] -> VTy -> [Name] -> (CheckArgs Val => [Val] -> M a) -> M a
    go revFields ty [] k =
      case ty of
        VPi {} -> report ("Wrong number of constructor fields for " ++ cname)
        _ -> k (reverse revFields)
    go revFields (VPi _ a b) (x : rest) k =
      ctxDefineNextVar x a $ \var ->
        go (var : revFields) (b ∙ var) rest k
    go _ _ _ _ = report ("Wrong number of constructor fields for " ++ cname)

inferCaseAltTy :: CheckArgs Val => [Val] -> ConInfo -> RawCaseAlt -> M VTy
inferCaseAltTy params ci (RawCaseAlt cname xs rawBody)
  | cname /= conName ci = report "Case constructors must match declaration order"
  | otherwise = do
      fty <- instantiateTyCon ci params
      withConFields cname fty xs (\_ -> snd <$> infer rawBody)

checkCaseAlt :: CheckArgs Val => [Val] -> Closure -> ConInfo -> RawCaseAlt -> M CaseAlt
checkCaseAlt params motive ci (RawCaseAlt cname xs rawBody)
  | cname /= conName ci = report "Case constructors must match declaration order"
  | otherwise = do
      fty <- instantiateTyCon ci params
      body <- withConFields cname fty xs $ \fields -> do
        let conVal = foldl doApp (globalLookup ?globals cname) (params ++ fields)
        check rawBody (motive ∙ conVal)
      pure (CaseAlt cname xs body)

checkCaseAlts :: CheckArgs Val => TyConInfo -> [Val] -> Closure -> [RawCaseAlt] -> M [CaseAlt]
checkCaseAlts tc params motive rawAlts = do
  cis <- orderedConInfos tc
  if length cis /= length rawAlts
    then report "Case expressions must cover all constructors in declaration order"
    else mapM (uncurry (checkCaseAlt params motive)) (zip cis rawAlts)

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
  (RCase scrut mmotive rawAlts, a') -> do
    (scrut', scrutTy) <- infer scrut
    (tc, params) <- expectTyCon scrutTy
    let scrutVal = eval scrut'
    (motName, motTm, motV) <- case mmotive of
      Just (x, rawB) -> do
        btm <- ctxDefineNextVar x scrutTy (\_ -> check rawB VU)
        pure (x, btm, Closure ?env btm)
      Nothing -> do
        btm <- ctxDefineNextVar "_" scrutTy (\_ -> pure (quote a'))
        pure ("_", btm, Closure ?env btm)
    alts <- checkCaseAlts tc params motV rawAlts
    unless (eq (motV ∙ scrutVal) a') $
      report ("type mismatch: " ++ show (motV ∙ scrutVal) ++ ", " ++ show a')
    pure (Case scrut' motName motTm alts)
  (RSplit rawAlts, VPi x dom cod) -> do
    (tc, params) <- expectTyCon dom
    motive <- ctxDefineNextVar x dom (\var -> pure (quote (cod ∙ var)))
    body <- ctxDefineNextVar x dom $ \_ -> do
      alts <- checkCaseAlts tc params cod rawAlts
      pure (Case (Var 0 []) x motive alts)
    pure (Lam x body)
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
  RCase scrut mmotive rawAlts -> do
    (scrut', scrutTy) <- infer scrut
    (tc, params) <- expectTyCon scrutTy
    let scrutVal = eval scrut'
    (motName, motTm, motV) <- case mmotive of
      Just (x, rawB) -> do
        btm <- ctxDefineNextVar x scrutTy (\_ -> check rawB VU)
        pure (x, btm, Closure ?env btm)
      Nothing -> do
        cis <- orderedConInfos tc
        case (cis, rawAlts) of
          (ci : _, alt : _) -> do
            a <- inferCaseAltTy params ci alt
            btm <- ctxDefineNextVar "_" scrutTy (\_ -> pure (quote a))
            pure ("_", btm, Closure ?env btm)
          _ -> report "Inferring case expression requires at least one branch"
    alts <- checkCaseAlts tc params motV rawAlts
    pure (Case scrut' motName motTm alts, motV ∙ scrutVal)
  RSplit {} -> report "Can't infer type for lambda-case"
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
        let global = findGlobalMaybe x
        maybe (report ("variable out of scope: " ++ x)) pure global
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

checkOrInferBody :: CheckArgs Val => Raw -> Maybe Raw -> M (Tm, Ty)
checkOrInferBody rhs Nothing = do
  (body, bty) <- infer rhs
  pure (body, quote bty)
checkOrInferBody rhs (Just rawRet) = do
  retty <- check rawRet VU
  body <- check rhs (eval retty)
  pure (body, retty)

withArgs :: CheckArgs Val => [RawArg] -> (CheckArgs Val => M (Tm, Ty)) -> M (Tm, Ty)
withArgs [] action = action
withArgs (RawArg x rawA : rest) action = do
  a <- check rawA VU
  ctxDefineNextVar x (eval a) $ \_ -> do
    (body, retty) <- withArgs rest action
    pure (Lam x body, Pi x a retty)

withArgsType :: CheckArgs Val => [RawArg] -> (CheckArgs Val => M Ty) -> M Ty
withArgsType [] action = action
withArgsType (RawArg x rawA : rest) action = do
  a <- check rawA VU
  ctxDefineNextVar x (eval a) $ \_ ->
    Pi x a <$> withArgsType rest action

inferTopDefNonRec :: CheckArgs Val => [RawArg] -> Maybe Raw -> Raw -> M (Tm, VTy)
inferTopDefNonRec args mret rhs = do
  (tm, ty) <- withArgs args (checkOrInferBody rhs mret)
  pure (tm, eval ty)

inferTopDefRec :: CheckArgs Val => Name -> [RawArg] -> Raw -> Raw -> M (Tm, VTy, Val)
inferTopDefRec x args rawRet rhs = do
  fullTy <- withArgsType args (check rawRet VU)
  let fullTyV = eval fullTy
      placeholder = VNeutral (NGlobalVar x)
  ctxDefineGlobal x placeholder fullTyV $ do
    (tm, _) <- withArgs args do
      ret <- check rawRet VU
      body <- check rhs (eval ret)
      pure (body, ret)
    pure (tm, fullTyV, eval tm)

inferCtor :: CheckArgs Val => TyConInfo -> [TelArg] -> Int -> RawCtor -> M (ConInfo, Ty)
inferCtor tc params idx (RawCtor c fieldsRaw) = do
  fields <- withRawArgs fieldsRaw pure
  let paramCount = length params
      fieldCount = length fields
      paramRef i = Var (Ix (fieldCount + (paramCount - i - 1))) []
      resultTy = foldl App (GlobalVar (tyConName tc)) [paramRef i | i <- [0 .. paramCount - 1]]
      cty = wrapPis (params ++ fields) resultTy
      ci = ConInfo c (tyConName tc) (length params) (length fields) idx
  pure (ci, cty)

inferCtors :: CheckArgs Val => TyConInfo -> [TelArg] -> Int -> [RawCtor] -> M [(ConInfo, Val, VTy)]
inferCtors _ _ _ [] = pure []
inferCtors tc params idx (ctor : rest) = do
  (ci, cty) <- inferCtor tc params idx ctor
  let cval =
        if conParamCount ci + conFieldCount ci == 0
          then VCon ci []
          else VConFun ci []
      cvty = eval cty
  rest' <- ctxDefineConInfo ci $ ctxDefineGlobal (conName ci) cval cvty $ inferCtors tc params (idx + 1) rest
  pure ((ci, cval, cvty) : rest')

inferTopInd :: CheckArgs Val => Name -> [RawArg] -> [RawCtor] -> M (Val, VTy, TyConInfo, [(ConInfo, Val, VTy)])
inferTopInd x paramsRaw ctorsRaw = withRawArgs paramsRaw $ \params -> do
  let ctorNames = [c | RawCtor c _ <- ctorsRaw]
      tc = TyConInfo x (length params) ctorNames
      tyconVal =
        if null params
          then VTyCon tc []
          else VTyConFun tc []
      tyconTy = eval (wrapPis params U)
  ctors <- ctxDefineTyConInfo tc $ ctxDefineGlobal x tyconVal tyconTy $ inferCtors tc params 0 ctorsRaw
  pure (tyconVal, tyconTy, tc, ctors)

withConEntries :: [(ConInfo, Val, VTy)] -> (CheckArgs Val => M a) -> (CheckArgs Val => M a)
withConEntries [] act = act
withConEntries ((ci, cval, cvty) : rest) act =
  withConEntries rest (ctxDefineConInfo ci $ ctxDefineGlobal (conName ci) cval cvty act)

inferTopDefs :: CheckArgs Val => [RawDecl] -> M Globals
inferTopDefs [] = pure ?globals
inferTopDefs (decl : rest) = case decl of
  RTopDef pos x args mty rhs -> let ?pos = pos in do
    case mty of
      Nothing -> do
        (tm, ty) <- inferTopDefNonRec args mty rhs
        ctxDefineGlobal x (eval tm) ty (inferTopDefs rest)
      Just rawRet -> do
        (_, ty, v) <- inferTopDefRec x args rawRet rhs
        ctxDefineGlobal x v ty (inferTopDefs rest)
  RTopInd pos x params ctors -> let ?pos = pos in do
    (tyconVal, tyconTy, tc, cons) <- inferTopInd x params ctors
    ctxDefineTyConInfo tc $
      ctxDefineGlobal x tyconVal tyconTy $
        withConEntries cons (inferTopDefs rest)

inferProgram :: CheckArgs Val => RawProgram -> M (Globals, Maybe (Tm, Ty))
inferProgram (RProgram defs mt) = do
  globals <- inferTopDefs defs
  case mt of
    Nothing -> pure (globals, Nothing)
    Just a  -> withGlobals globals $ do
      (t, vty) <- infer a
      pure (globals, Just (t, quote vty))
