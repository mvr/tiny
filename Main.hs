-- An unholy combination of
-- https://github.com/AndrasKovacs/elaboration-zoo/blob/master/02-typecheck-closures-debruijn/Main.hs
-- https://github.com/jozefg/blott/blob/master/src/lib
-- https://github.com/AndrasKovacs/cctt/tree/main/src
-- https://github.com/RedPRL/cooltt/tree/main/src/core
-- https://davidchristiansen.dk/tutorials/implementing-types-hs.pdf

module Main where

-- import Debug.Trace

import Control.Monad (unless, guard)
import Data.Char
import Data.Coerce
import Data.Maybe (fromMaybe)
import Data.Void
import System.Environment
import System.Exit
import Text.Megaparsec
import qualified Text.Megaparsec.Char as C
import qualified Text.Megaparsec.Char.Lexer as L
import Text.Printf
import Prelude hiding (lookup)

newtype Ix = Ix Int deriving (Eq, Show, Num) via Int
newtype Lvl = Lvl Int deriving (Eq, Ord, Show, Num) via Int
-- and | GenLvl Int ?

type Name = String

type LockName = String

data Raw
  = RU
  | RLet Name Raw Raw Raw
  | RPi Name Raw Raw
  | RLam Name Raw
  | RApp Raw Raw
  | RSg Name Raw Raw
  | RPair Raw Raw
  | RFst Raw
  | RSnd Raw
  | RSrcPos SourcePos Raw -- source position for error reporting

  ---- New:
  | RVar Name [Raw]
  | RTiny
  | RRoot LockName Raw
  | RRootIntro LockName Raw
  | RRootElim Name Raw
  deriving (Show)

-- core syntax
------------------------------------------------------------

type Ty = Tm

data Tm
  = U
  | Let Name Ty Tm Tm
  | Pi Name Ty Ty
  | Lam Name Tm
  | App Tm Tm
  | Sg Name Ty Ty
  | Pair Tm Tm
  | Fst Tm
  | Snd Tm

  ---- New:
  | Var Ix [Tm]
  | Tiny
  -- | Key Tm Tm
  | Root LockName Ty
  | RootIntro LockName Tm
  | RootElim Name Tm

-- values
------------------------------------------------------------

data EnvVars v =
  EnvEmpty
  | EnvVal v (EnvVars v)
  | EnvLock (Val -> EnvVars v)

data Env v = Env
  { envVars   :: EnvVars v,
    envLength :: Int,
    envFresh  :: Lvl }
  deriving (Show, Functor)

emptyEnv :: Env v
emptyEnv = Env EnvEmpty 0 0

instance Show v => Show (EnvVars v) where
  showsPrec d EnvEmpty = showString "EnvEmpty"
  showsPrec d (EnvVal v env) = showParen (d > 10) $
    showString "EnvVal "
      . showsPrec 11 v
      . showString " "
      . showsPrec 11 env
  showsPrec d (EnvLock fenv) = showParen (d > 10) $
    showString "EnvLock "
      -- . showsPrec 11 "..."
      . showsPrec 11 (fenv (VNeutral VTiny (NVar (Lvl $ 1000) VTiny [])))

-- Just derive this
instance Functor EnvVars where
  fmap f EnvEmpty = EnvEmpty
  fmap f (EnvVal v env) = EnvVal (f v) (fmap f env)
  fmap f (EnvLock fenv) = EnvLock (\v -> fmap f (fenv v))

makeVarLvl :: Lvl -> VTy -> Val
makeVarLvl lvl a = VNeutral a (NVar lvl a [])

makeVar :: Env v -> VTy -> Val
makeVar env a = makeVarLvl (Lvl $ envLength env) a

lvl2Ix :: Env v -> Lvl -> Ix
lvl2Ix env (Lvl x) = Ix (envLength env - x - 1)

ix2Lvl :: Env v -> Ix -> Lvl
ix2Lvl env (Ix x) = Lvl (envLength env - x - 1)

extVal :: Env v -> v -> Env v
extVal env v = env { envVars = EnvVal v (envVars env),
                     envLength = 1 + envLength env,
                     envFresh = 1 + envFresh env }

extStuck :: Keyable v => Env v -> Env v
extStuck env = env { envVars = EnvLock (\v -> addKey (envFresh env) v (envVars env)),
                     envLength = 1 + envLength env,
                     envFresh = 1 + envFresh env }

extUnit :: Lvl -> Env Val -> Env Val
extUnit lvl env = env { envVars = EnvLock (\v -> sub (envFresh env) v lvl (envVars env)),
                        envLength = 1 + envLength env,
                        envFresh = 1 + envFresh env }

data Closure = Closure (Env Val) Tm
  deriving (Show)

data RootClosure = RootClosure (Env Val) Tm
  deriving (Show)

data BindTiny a = BindTiny Name Lvl a
  deriving (Show)

type VTy = Val

data Val
  = VNeutral VTy Neutral
  | VU
  | VPi Name VTy Closure
  | VLam Name Closure
  | VSg Name VTy Closure
  | VPair Val Val
  ---- New:
  | VTiny
  | VRoot LockName RootClosure
  | VRootIntro LockName RootClosure
  deriving (Show)

data Neutral
  = NVar Lvl VTy [Val]
  | NApp Neutral Normal
  | NFst Neutral
  | NSnd Neutral
  ---- New:
  | NRootElim (BindTiny Neutral)
  deriving (Show)

data Normal = Normal {nfTy :: VTy, nfTerm :: Val}
  deriving (Show)

class Apply a b c | a -> b c where
  apply :: Lvl -> a -> b -> c

instance Apply Closure Val Val where
  apply fr (Closure cloenv t) u =
    let newEnv = (extVal cloenv u) { envFresh = max (envFresh cloenv) fr } in
      eval newEnv t

instance (Show a, Renameable a) => Apply (BindTiny a) Lvl a where
  apply fr (BindTiny l i a) j
    | i == j    = a
    | otherwise = rename j i a

class CoApply a b c | a -> b c where
  coapply :: Lvl -> a -> b -> c

instance CoApply RootClosure Lvl Val where
  coapply fr (RootClosure cloenv t) lvl =
    let newEnv = (extUnit lvl cloenv) { envFresh = max (envFresh cloenv) fr } in
      eval newEnv t

appRootClosureStuck :: RootClosure -> Val
appRootClosureStuck (RootClosure cloenv t) = eval (extStuck cloenv) t

-- substitutions
------------------------------------------------------------

-- TODO: "NVar and EnvLock are the only interesting cases" is this true?

-- Appends keys to all free variables
-- This cannot cause reduction
class Keyable a where
  addKeys :: Lvl -> [Val] -> a -> a
  addKey :: Lvl -> Val -> a -> a
  addKey fr k = addKeys fr [k]

instance Keyable Name where
  addKeys fr ks n = n

instance (Keyable a, Keyable b) => Keyable (a, b) where
  addKeys fr ks (a, b) = (addKeys fr ks a, addKeys fr ks b)

instance (Keyable a, Keyable b, Keyable c) => Keyable (a, b, c) where
  addKeys fr ks (a, b, c) = (addKeys fr ks a, addKeys fr ks b, addKeys fr ks c)

instance Keyable Val where
  addKeys fr ks = \case
    VNeutral ty n -> VNeutral (addKeys fr ks ty) (addKeys fr ks n)
    VU -> VU
    VPi x a b -> VPi x (addKeys fr ks a) (addKeys fr ks b)
    VLam x c -> VLam x (addKeys fr ks c)
    VSg x a b -> VSg x (addKeys fr ks a) (addKeys fr ks b)
    VPair x y -> VPair (addKeys fr ks x) (addKeys fr ks y)
    VTiny -> VTiny
    VRoot l c -> VRoot l (addKeys fr ks c)
    VRootIntro l c -> VRootIntro l (addKeys fr ks c)

instance Keyable Neutral where
  addKeys fr ks = \case
    NVar lvl ty keys -> NVar lvl (addKeys fr ks ty) (ks ++ fmap (addKeys fr ks) keys)
    NApp f a -> NApp (addKeys fr ks f) (addKeys fr ks a)
    NFst a -> NFst (addKeys fr ks a)
    NSnd a -> NSnd (addKeys fr ks a)
    NRootElim (BindTiny l lvl n) -> undefined -- NRootElim (BindTiny l lvl (addKeys fr ks n))

instance Keyable Normal where
  addKeys fr ks (Normal ty a) = Normal (addKeys fr ks ty) (addKeys fr ks a)

instance Keyable Closure where
  addKeys fr ks (Closure env t) = Closure (addKeys fr ks env) t

instance Keyable RootClosure where
  addKeys fr ks (RootClosure env t) = RootClosure (addKeys fr ks env) t

instance Keyable v => Keyable (EnvVars v) where
  addKeys fr ks EnvEmpty = EnvEmpty
  addKeys fr ks (EnvVal v env) = EnvVal (addKeys fr ks v) (addKeys fr ks env)
  addKeys fr ks (EnvLock f) = EnvLock (addKeys fr ks . f)

instance Keyable v => Keyable (Env v) where
  addKeys fr ks env = env { envFresh = max (envFresh env) (coerce fr),
                            envVars = addKeys fr ks (envVars env) }

-- Substitutes a value for a variable
-- This may cause reduction
-- so Neutral -> Val and Normal -> Val
class Substitutable a b | a -> b where
  sub :: Lvl -> Val -> Lvl -> a -> b

instance Substitutable Val Val where
  sub fr v i = \case
    VNeutral ty n -> sub fr v i n
    VU -> VU
    VPi x a b -> VPi x (sub fr v i a) (sub fr v i b)
    VLam x c -> VLam x (sub fr v i c)
    VSg x a b -> VSg x (sub fr v i a) (sub fr v i b)
    VPair a b -> VPair (sub fr v i a) (sub fr v i b)
    VTiny -> VTiny
    VRoot l c -> VRoot l (sub fr v i c)
    VRootIntro l c -> VRootIntro l (sub fr v i c)

instance Substitutable Neutral Val where
  sub fr v i = \case
    var@(NVar j ty ks) | i == j -> addKeys fr (fmap (sub fr v i) ks) v
                       | otherwise -> VNeutral subty (NVar j subty (fmap (sub fr v i) ks)) where subty = sub fr v i ty
    NApp f a -> apply fr (sub fr v i f) (sub fr v i a)
    NFst a -> doFst (sub fr v i a)
    NSnd b -> doSnd fr (sub fr v i b)
    NRootElim (BindTiny x lvl n) -> undefined -- sub fr v i (rename fresh lvl n) ↬ fresh
      where fresh = Lvl undefined
    -- TODO: what if v contains NVars with level larger than size? Need to freshen the binder past all those too

instance Substitutable Normal Val where
  sub fr v i (Normal ty a) = sub fr v i a

instance Substitutable Closure Closure where
  sub fr v i (Closure env t) = Closure (sub fr v i env) t

instance Substitutable RootClosure RootClosure where
  sub fr v i (RootClosure env t) = RootClosure (sub fr v i env) t

-- instance Substitutable v v' => Substitutable (Env v) (Env v') where
instance Substitutable (EnvVars Val) (EnvVars Val) where
  sub fr v i EnvEmpty = EnvEmpty
  sub fr v i (EnvVal e env) = EnvVal (sub fr v i e) (sub fr v i env)
  sub fr v i (EnvLock f) = EnvLock (sub fr v i . f)

instance Substitutable (Env Val) (Env Val) where
  sub fr v i env = env { envFresh = max (envFresh env) (coerce fr),
                         envVars  = sub fr v i (envVars env) }

-- Switch one de Bruijn level for another
-- The variables have the same types,
-- so this cannot cause reduction
class Renameable a where
  rename :: Lvl -> Lvl -> a -> a

instance Renameable Val where
  rename v i = \case
    VNeutral ty n -> VNeutral (rename v i ty) (rename v i n)
    VU -> VU
    VPi x a b -> VPi x (rename v i a) (rename v i b)
    VLam x c -> VLam x (rename v i c)
    VSg x a b -> VSg x (rename v i a) (rename v i b)
    VPair a b -> VPair (rename v i a) (rename v i b)
    VTiny -> VTiny
    VRoot l c -> VRoot l (rename v i c)
    VRootIntro l c -> VRootIntro l (rename v i c)

instance Renameable Neutral where
  rename v i = \case
    NVar j ty ks | i == j -> NVar v (rename v i ty) (fmap (rename v i) ks)
                 | otherwise -> NVar j (rename v i ty) (fmap (rename v i) ks)
    NApp f a -> NApp (rename v i f) (rename v i a)
    NRootElim bt -> NRootElim (rename v i bt)
    NFst a -> NFst (rename v i a)
    NSnd a -> NSnd (rename v i a)

instance Renameable Normal where
  rename v i (Normal ty a) = Normal (rename v i ty) (rename v i a)

instance Renameable Closure where
  rename v i (Closure env t) = Closure (rename v i env) t

instance Renameable RootClosure where
  rename v i (RootClosure env t) = RootClosure (rename v i env) t

instance Renameable a => Renameable (BindTiny a) where
  rename v i (BindTiny l j a) = undefined
    -- | v == j = BindTiny l j (rename v i a) -- TODO: freshen
    -- | otherwise = BindTiny l j (rename v i a)

instance Renameable v => Renameable (EnvVars v) where
  rename v i EnvEmpty = EnvEmpty
  rename v i (EnvVal e env) = EnvVal (rename v i e) (rename v i env)
  rename v i (EnvLock f) = EnvLock (rename v i . f)

instance Renameable (Env Val) where
  rename v i env = env {
    envFresh = max (envFresh env) (1 + coerce v),
    envVars = rename v i (envVars env)
    }

-- evaluation
------------------------------------------------------------

doApp :: Lvl -> Val -> Val -> Val
doApp fr (VLam _ t) u = apply fr t u
doApp fr (VNeutral (VPi x aty bclo) ne) a = VNeutral (apply fr bclo a) (NApp ne (Normal aty a))
doApp fr t u = error $ "Unexpected in App: " ++ show t ++ " applied to " ++ show u

instance Apply Val Val Val where
  apply = doApp

doFst :: Val -> Val
doFst (VPair a b) = a
doFst (VNeutral (VSg x aty _) ne) = VNeutral aty (NFst ne)
doFst t = error $ "Unexpected in fst: " ++ show t

doSnd :: Lvl -> Val -> Val
doSnd fr (VPair a b) = b
doSnd fr p@(VNeutral (VSg x aty bclo) ne) =
  let a = doFst p in VNeutral (apply fr bclo a) (NSnd ne)
doSnd fr t = error $ "Unexpected in snd: " ++ show t

doRootElim :: Lvl -> Val -> Lvl -> Val
doRootElim fr (VRootIntro l c) lvl = coapply fr c lvl
doRootElim fr (VNeutral (VRoot l c) ne) lvl = VNeutral (coapply fr c lvl) (NRootElim (BindTiny "geni" lvl ne))
doRootElim fr v lvl = error $ "Unexpected in relim: " ++ show v

instance CoApply Val Lvl Val where
  coapply = doRootElim

doRootElimEta :: Env v -> Val -> Val
doRootElimEta env r =
  let lvl = envFresh env
  in doRootElim (lvl + 1) (addKey (lvl+1) (makeVarLvl lvl VTiny) r) lvl

envLookup :: EnvVars v -> Ix -> [Val] -> v
envLookup env i keys = go i keys env
  where go 0 keys (EnvVal v envtail) = v
        go i keys (EnvVal v envtail) = go (i-1) keys envtail
        go i (k : keys) (EnvLock f) = go (i-1) keys (f k)
        go i [] (EnvLock f) = error "Ran out of keys"
        go _ _ EnvEmpty = error "Ran out of environment"

eval :: Env Val -> Tm -> Val
-- eval env t = traceShow (env, t) $ case t of
eval env t = case t of
  U                           -> VU
  Let x _ t u                 -> eval (env `extVal` eval env t) u

  Pi x a b                    -> VPi x (eval env a) (Closure env b)
  Lam x t                     -> VLam x (Closure env t)
  App t u                     -> apply (envFresh env) (eval env t) (eval env u)

  Sg x a b                    -> VSg x (eval env a) (Closure env b)
  Pair a b                    -> VPair (eval env a) (eval env b)
  Fst a                       -> doFst (eval env a)
  Snd a                       -> doSnd (envFresh env) (eval env a)

  ---- New:
  Var x keys                  -> envLookup (envVars env) x (fmap (eval env) keys)
  Tiny                        -> VTiny
  Root l a                    -> VRoot l (RootClosure env a)
  RootIntro l t               -> VRootIntro l (RootClosure env t)
  RootElim x t                -> let lvl = envFresh env in coapply (1+lvl) (eval (env `extVal` makeVarLvl lvl VTiny) t) lvl


quoteType :: Env Val -> VTy -> Tm
quoteType env = \case
  (VNeutral _ ne)              -> quoteNeutral env ne
  VU                           -> U
  VPi x a b                    -> Pi x (quoteType env a) (let var = makeVar env a in quoteType (env `extVal` var) (apply (1+envFresh env) b var))
  VSg x a b                    -> Sg x (quoteType env a) (let var = makeVar env a in quoteType (env `extVal` var) (apply (1+envFresh env) b var))

  ---- New:
  VTiny                        -> Tiny
  VRoot l a                    -> Root l (quoteType (extStuck env) (appRootClosureStuck a))
  t                            -> error ("type expected, got " ++ show t)

quote :: Env Val -> VTy -> Val -> Tm
quote env = \cases
  VU vty                         -> quoteType env vty
  (VPi _ a b) (VLam x c)         -> Lam x (let var = makeVar env a in quote (env `extVal` var) (apply (1+envFresh env) b var) (apply (1+envFresh env) c var))
  (VPi x a b) f                  -> Lam x (let var = makeVar env a in quote (env `extVal` var) (apply (1+envFresh env) b var) (apply (1+envFresh env) f var))

  ---- New:
  -- (VRoot _ a) (VRootIntro l c)   -> RootIntro l (quote (extStuck env)
  --                                                      (appRootClosureStuck a)
  --                                                      (doRootElimEta env _))
  (VRoot l a) r                  -> RootIntro l (quote (extStuck env)
                                                       (appRootClosureStuck a)
                                                       (doRootElimEta env r))

  -- For debugging
  ty (VNeutral tyne ne)          -> if not (eqTy env ty tyne) then
                                      error $ "neutral type mismatch: " ++ show ty  ++ ", " ++ show tyne
                                    else
                                      quoteNeutral env ne
  -- _ (VNeutral _ ne)              -> quoteNeutral env ne

  _ _                            -> error "Can't quote"

quoteNeutral :: Env Val -> Neutral -> Tm
quoteNeutral env (NVar x ty keys) = Var (lvl2Ix env x) (fmap (quote env VTiny) keys)
quoteNeutral env (NApp f (Normal aty a)) = App (quoteNeutral env f) (quote env aty a)
quoteNeutral env (NFst a) = Fst (quoteNeutral env a)
quoteNeutral env (NSnd a) = Snd (quoteNeutral env a)
quoteNeutral env (NRootElim bt@(BindTiny l lvl r)) = RootElim l (let lvl = envFresh env in quoteNeutral (env `extVal` makeVarLvl lvl VTiny) (apply (1+lvl) bt lvl))

nf :: Env Val -> VTy -> Tm -> Tm
nf env a t = quote env a (eval env t)

-- conversion
------------------------------------------------------------

eqTy :: Env Val -> VTy -> VTy -> Bool
-- eqTy env p1 p2 | traceShow ("eqTy:", p1, p2) False = undefined
eqTy env VU VU =True
eqTy env (VNeutral _ ne1) (VNeutral _ ne2) = eqNE env ne1 ne2
eqTy env (VPi _ aty1 bclo1) (VPi _ aty2 bclo2) =
  let var = makeVar env aty1
   in eqTy env aty1 aty2
        && eqTy (env `extVal` var) (apply (1+envFresh env) bclo1 var) (apply (1+envFresh env) bclo2 var)
eqTy env (VSg _ aty1 bclo1) (VSg _ aty2 bclo2) =
  let var = makeVar env aty1
   in eqTy env aty1 aty2
        && eqTy (env `extVal` var) (apply (1+envFresh env) bclo1 var) (apply (1+envFresh env) bclo2 var)
eqTy env VTiny VTiny = True
eqTy env (VRoot _ a) (VRoot _ a') = eqTy (extStuck env) (appRootClosureStuck a) (appRootClosureStuck a')
eqTy _ _ _ = False

eqNF :: Env Val -> (VTy, Val) -> (VTy, Val) -> Bool
-- eqNF env p1 p2 | traceShow ("eqNF:", p1, p2) False = undefined
eqNF env (VU, ty1) (VU, ty2) = eqTy env ty1 ty2
eqNF env (VPi _ aty1 bclo1, f1) (VPi _ aty2 bclo2, f2) =
  let var = makeVar env aty1
   in eqNF (env `extVal` var) (apply (1 + envFresh env) bclo1 var, apply (1 + envFresh env) f1 var) (apply (1 + envFresh env) bclo2 var, apply (1 + envFresh env) f2 var)
eqNF env (VSg _ aty1 bclo1, p1) (VSg _ aty2 bclo2, p2) =
  let a1 = doFst p1
      a2 = doFst p2
  in eqNF env (aty1, a1) (aty2, a2) &&
     eqNF env (apply (envFresh env) bclo1 a1, doSnd (envFresh env) p1) (apply (envFresh env) bclo2 a2, doSnd (envFresh env) p2)
eqNF env (VRoot _ a1, r1) (VRoot _ a2, r2) =
  eqNF (extStuck env)
       (appRootClosureStuck a1, doRootElimEta env r1)
       (appRootClosureStuck a2, doRootElimEta env r2)
eqNF env (_, VNeutral _ ne1) (_, VNeutral _ ne2) = eqNE env ne1 ne2
eqNF _ _ _ = False

eqNE :: Env Val -> Neutral -> Neutral -> Bool
-- eqNE env p1 p2 | traceShow ("eqNE:", p1, p2) False = undefined
eqNE env (NVar i ity ikeys) (NVar j jty jkeys) = i == j && all (uncurry keyeq) (zip ikeys jkeys)
  where keyeq ik jk = eqNF env (VTiny, ik) (VTiny, jk)
eqNE env (NApp f1 (Normal aty1 a1)) (NApp f2 (Normal aty2 a2)) =
  eqNE env f1 f2 && eqNF env (aty1, a1) (aty2, a2)
eqNE env (NFst p1) (NFst p2) = eqNE env p1 p2
eqNE env (NSnd p1) (NSnd p2) = eqNE env p1 p2
eqNE env (NRootElim tb1) (NRootElim tb2) = eqNE (env `extVal` var) (apply (1 + envFresh env) tb1 lvl) (apply (1 + envFresh env) tb2 lvl)
  where lvl = envFresh env
        var = makeVarLvl lvl VTiny
eqNE _ ne1 ne2 = False

-- type checking
------------------------------------------------------------

-- | Typechecking monad. We annotate the error with the current source position.
type M = Either (String, SourcePos)

-- | Elaboration context.
data Ctx = Ctx {env :: Env (Name, Val, VTy), pos :: SourcePos}
  deriving (Show)
-- names :: Ctx -> [String]
-- names ctx = fmap (either id fst) (types ctx)

emptyCtx :: SourcePos -> Ctx
emptyCtx = Ctx (Env EnvEmpty 0 0)

ctxVals :: Ctx -> Env Val
ctxVals = fmap (\(_,x,_) -> x) . env

ctxLength :: Ctx -> Int
ctxLength = envLength . env

define :: Name -> Val -> VTy -> Ctx -> Ctx
define x v a (Ctx env pos) = Ctx (env `extVal` (x, v, a)) pos

bind :: Name -> VTy -> Ctx -> Ctx
bind x a ctx = define x (makeVar (env ctx) a) a ctx

bindStuckLock :: Name -> Ctx -> Ctx
bindStuckLock l (Ctx env pos) = Ctx (extStuck env) pos

report :: Ctx -> String -> M a
report ctx msg = Left (msg, pos ctx)

-- showVal :: Ctx -> VTy -> Val -> String
-- showVal ctx a v = prettyTm 0 (names ctx) (quote (env ctx) a v) []

check :: Ctx -> Raw -> VTy -> M Tm
check ctx t a = case (t, a) of
-- check ctx t a = traceShow (t, a) $ case (t, a) of
-- check ctx t a = traceShow (ctx, t, a) $ case (t, a) of
  (RSrcPos pos t, a) -> check (ctx {pos = pos}) t a

  (RLet x a t u, a') -> do
    a <- check ctx a VU
    let va = eval (ctxVals ctx) a
    t <- check ctx t va
    let vt = eval (ctxVals ctx) t
    u <- check (define x vt va ctx) u a'
    pure (Let x a t u)

  (RLam x t, VPi x' a b) ->
    Lam x <$> check (bind x a ctx) t (apply (1 + Lvl (ctxLength ctx)) b (makeVar (env ctx) a))

  (RPair a b, VSg x aty bty) -> do
    a <- check ctx a aty
    b <- check ctx b (apply (1 + Lvl (ctxLength ctx)) bty (eval (ctxVals ctx) a))
    pure (Pair a b)

  ---- New:

  (RRootIntro x t, VRoot x' a)
    -> RootIntro x <$> check (bindStuckLock x ctx) t (appRootClosureStuck a)

  _ -> do
    (t, tty) <- infer ctx t
    unless (eqTy (ctxVals ctx) tty a) $
     report ctx ("type mismatch: " ++ show tty  ++ ", " ++ show a)
    pure t

infer :: Ctx -> Raw -> M (Tm, VTy)
infer ctx r = case r of
-- infer ctx r = traceShow r $ case r of
-- infer ctx r = traceShow (ctx, r) $ case r of
  RSrcPos pos t -> infer (ctx {pos = pos}) t

  RU -> pure (U, VU)   -- U : U rule

  RLet x a t u -> do
    a <- check ctx a VU
    let va = eval (ctxVals ctx) a
    t <- check ctx t va
    let vt = eval (ctxVals ctx) t
    (u, uty) <- infer (define x vt va ctx) u
    pure (Let x a t u, uty)

  RPi x a b -> do
    a <- check ctx a VU
    b <- check (bind x (eval (ctxVals ctx) a) ctx) b VU
    pure (Pi x a b, VU)

  RApp t u -> do
    (t, tty) <- infer ctx t
    case tty of
      VPi _ a b -> do
        u <- check ctx u a
        pure (App t u, apply (Lvl $ ctxLength ctx) b (eval (ctxVals ctx) u))
      tty ->
        report ctx $ "Expected a function type, instead inferred:\n\n  " ++ "todo" -- showVal ctx tty

  RLam{} -> report ctx "Can't infer type for lambda expression"

  RSg x a b -> do
    a <- check ctx a VU
    b <- check (bind x (eval (ctxVals ctx) a) ctx) b VU
    pure (Sg x a b, VU)

  RPair{} -> report ctx "Can't infer type for pair"

  RFst p -> do
    (t, ty) <- infer ctx p
    case ty of
      VSg x a b -> pure (Fst t, a)
      _ -> report ctx $ "expected Sg type"

  RSnd p -> do
    (t, ty) <- infer ctx p
    case ty of
      VSg x a b -> pure (Snd t, apply (Lvl $ ctxLength ctx) b (eval (ctxVals ctx) (Fst t)))
      _ -> report ctx $ "expected Sg type"

  ---- New:
  RVar x rkeys -> do
    let go i EnvEmpty _ = report ctx ("variable out of scope: " ++ x)
        go i (EnvVal (x', v, ty) env) keys
          | x == x'   = case keys of
                          [] -> do
                            keyst <- mapM (\key -> check ctx key VTiny) rkeys
                            pure (Var i keyst, ty)
                          _  -> report ctx ("too many keys provided: " ++ x)
          | otherwise = go (i + 1) env keys
        go i (EnvLock env) [] = report ctx ("not enough keys provided: " ++ x)
        go i (EnvLock fenv) (key:keys) = do
          keyt <- check ctx key VTiny
          let keyv = eval (ctxVals ctx) keyt
          go (i+1) (fenv keyv) keys
    go 0 (envVars $ env ctx) rkeys

  RTiny -> pure (Tiny, VU)

  RRoot l a -> do
    a <- check (bindStuckLock l ctx) a VU
    pure (Root l a, VU)

  RRootElim x t -> do
    (t, tty) <- infer (bind x VTiny ctx) t
    case tty of
      VRoot _ c -> do
          pure (RootElim x t, coapply (Lvl $ ctxLength ctx) c (Lvl $ ctxLength ctx))
      tty ->
        report ctx $ "Expected a root type, instead inferred:\n\n  " ++ "todo" -- showVal ctx tty

  RRootIntro{} -> report ctx "Can't infer type for rintro expression"

-- printing
--------------------------------------------------------------------------------

fresh :: [Name] -> Name -> Name
fresh ns "_" = "_"
fresh ns x | elem x ns = fresh ns (x ++ "'")
           | otherwise = x

-- printing precedences
atomp = 3  :: Int -- U, var
appp  = 2  :: Int -- application
pip   = 1  :: Int -- pi
letp  = 0  :: Int -- let, lambda

-- | Wrap in parens if expression precedence is lower than
--   enclosing expression precedence.
par :: Int -> Int -> ShowS -> ShowS
par p p' = showParen (p' < p)

prettyTm :: Int -> [Name] -> Tm -> ShowS
prettyTm prec = go prec where

  piBind ns x a =
    showParen True ((x++) . (" : "++) . go letp ns a)

  go :: Int -> [Name] -> Tm -> ShowS
  go p ns = \case
    U                         -> ("U"++)

    Let (fresh ns -> x) a t u -> par p letp $ ("let "++) . (x++) . (" : "++) . go letp ns a
                                 . ("\n    = "++) . go letp ns t . ("\nin\n"++) . go letp (x:ns) u

    Pi "_" a b                -> par p pip $ go appp ns a . (" → "++) . go pip ("_":ns) b

    Pi (fresh ns -> x) a b    -> par p pip $ piBind ns x a . goPi (x:ns) b where
                                   goPi ns (Pi "_" a b) =
                                     (" → "++) . go appp ns a . (" → "++) . go pip ("_":ns) b
                                   goPi ns (Pi (fresh ns -> x) a b) =
                                     piBind ns x a . goPi (x:ns) b
                                   goPi ns b =
                                     (" → "++) . go pip ns b

    Lam (fresh ns -> x) t     -> par p letp $ ("λ "++) . (x++) . goLam (x:ns) t where
                                   goLam ns (Lam (fresh ns -> x) t) =
                                     (' ':) . (x++) . goLam (x:ns) t
                                   goLam ns t =
                                     (". "++) . go letp ns t

    App t u                   -> par p appp $ go appp ns t . (' ':) . go atomp ns u

    Sg "_" a b                -> par p pip $ go appp ns a . (" × "++) . go pip ("_":ns) b

    Sg (fresh ns -> x) a b    -> par p pip $ piBind ns x a . goSg (x:ns) b where
                                   goSg ns (Sg "_" a b) =
                                     (" × "++) . go appp ns a . (" × "++) . go pip ("_":ns) b
                                   goSg ns (Sg (fresh ns -> x) a b) =
                                     piBind ns x a . goSg (x:ns) b
                                   goSg ns b =
                                     (" × "++) . go pip ns b

    Pair a b                  -> ("<" ++) . go letp ns a . (", " ++) . go letp ns b . (">" ++)
    Fst a                     -> par p letp $ ("fst " ++) . go letp ns a
    Snd a                     -> par p letp $ ("snd " ++) . go letp ns a

    Var (Ix x) []             -> ((ns !! x)++)
    Var (Ix x) keys           -> ((ns !! x)++) . ('[':) . goKeys keys . (']':) where
                                   goKeys [] = id
                                   goKeys [k] = go p ns k
                                   goKeys (k:ks) = go p ns k . (", " ++) . goKeys ks

    Tiny                      -> ("T"++)
    Root (fresh ns -> x) a    -> par p pip $ ("√ " ++) . (x++) . (". "++) . go pip (x:ns) a
    RootIntro (fresh ns -> x) t -> par p letp $ ("rintro " ++) . (x++) . (". "++) . go letp (x:ns) t
    RootElim (fresh ns -> x) t -> par p letp $ ("relim "++) . (x++) . (". "++) . go letp (x:ns) t

-- deriving instance Show Tm
instance Show Tm where showsPrec p = prettyTm p []


-- parsing
------------------------------------------------------------

type Parser = Parsec Void String

ws :: Parser ()
ws = L.space C.space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

withPos :: Parser Raw -> Parser Raw
-- withPos p = RSrcPos <$> getSourcePos <*> p
withPos p = p

lexeme   = L.lexeme ws
symbol s = lexeme (C.string s)
char c   = lexeme (C.char c)
parens p = char '(' *> p <* char ')'
pArrow   = symbol "→" <|> symbol "->"
pTimes   = symbol "×" <|> symbol "*"
pSurd    = symbol "√" <|> symbol "v/" -- TODO will v get mistaken for an ident?

keyword :: String -> Bool
keyword x = x == "let" || x == "in" || x == "λ" || x == "U" || x == "T" || x == "rintro" || x == "relim" || x == "fst" || x == "snd"

pIdent :: Parser Name
pIdent = try $ do
  x <- (:) <$> C.letterChar <*> many (C.alphaNumChar <|> char '_') -- takeWhile1P Nothing isAlphaNum
  guard (not (keyword x))
  x <$ ws

pKeyword :: String -> Parser ()
pKeyword kw = do
  C.string kw
  (takeWhile1P Nothing isAlphaNum *> empty) <|> ws

pKeyList :: Parser [Raw]
pKeyList = do
  symbol "["
  keys <- sepBy pRaw (symbol ",")
  symbol "]"
  pure keys

pVar :: Parser Raw
pVar = do
  i <- pIdent
  keys <- fromMaybe [] <$> optional pKeyList
  pure (RVar i keys)

pAtom :: Parser Raw
pAtom =
      withPos (pVar <|> (RU <$ symbol "U") <|> (RTiny <$ symbol "T"))
  <|> parens pRaw

pBinder = pIdent <|> symbol "_"
pSpine  = foldl1 RApp <$> some pAtom

pPi = do
  dom <- some (parens ((,) <$> some pBinder <*> (char ':' *> pRaw)))
  pArrow
  cod <- pRaw
  pure $ foldr (\(xs, a) t -> foldr (\x -> RPi x a) t xs) cod dom

pLam = do
  char 'λ' <|> char '\\'
  xs <- some pBinder
  char '.'
  t <- pRaw
  pure (foldr RLam t xs)

pSg = do
  dom <- some (parens ((,) <$> some pBinder <*> (char ':' *> pRaw)))
  pTimes
  cod <- pRaw
  pure $ foldr (\(xs, a) t -> foldr (\x -> RSg x a) t xs) cod dom

pPair = do
  symbol "<"
  a <- pRaw
  symbol ","
  b <- pRaw
  symbol ">"
  return (RPair a b)

pFst = do
  symbol "fst"
  t <- pRaw
  pure (RFst t)

pSnd = do
  symbol "snd"
  t <- pRaw
  pure (RSnd t)

pRoot = do
  pSurd
  xs <- pBinder
  char '.'
  t <- pRaw
  pure (RRoot xs t)

pRootIntro = do
  symbol "rintro"
  xs <- pBinder
  char '.'
  t <- pRaw
  pure (RRootIntro xs t)

pRootElim = do
  symbol "relim"
  xs <- pBinder
  char '.'
  t <- pRaw
  pure (RRootElim xs t)

funOrSpine = do
  sp <- pSpine
  optional pArrow >>= \case
    Nothing -> optional pTimes >>= \case
      Nothing -> pure sp
      Just _  -> RSg "_" sp <$> pRaw
    Just _  -> RPi "_" sp <$> pRaw

pLet = do
  pKeyword "let"
  x <- pBinder
  symbol ":"
  a <- pRaw
  symbol "="
  t <- pRaw
  symbol ";"
  u <- pRaw
  pure $ RLet x a t u

pRaw = withPos (pLam <|> pPair <|> pFst <|> pSnd <|> pLet <|> pRoot <|> pRootIntro <|> pRootElim <|> try pPi <|> try pSg <|> funOrSpine)
pSrc = ws *> pRaw <* eof

parseString :: String -> IO Raw
parseString src =
  case parse pSrc "(stdin)" src of
    Left e -> do
      putStrLn $ errorBundlePretty e
      exitSuccess
    Right t ->
      pure t

parseStdin :: IO (Raw, String)
parseStdin = do
  file <- getContents
  tm   <- parseString file
  pure (tm, "(stdin)")

parseFile :: String -> IO (Raw, String)
parseFile fn = do
  file <- readFile fn
  tm   <- parseString file
  pure (tm, fn)

-- -- main
-- ------------------------------------------------------------

displayError :: String -> (String, SourcePos) -> IO ()
displayError file (msg, SourcePos path (unPos -> linum) (unPos -> colnum)) = do
  let lnum = show linum
      lpad = map (const ' ') lnum
  printf "%s:%d:%d:\n" path linum colnum
  printf "%s |\n"    lpad
  printf "%s | %s\n" lnum (lines file !! (linum - 1))
  printf "%s | %s\n" lpad (replicate (colnum - 1) ' ' ++ "^")
  printf "%s\n" msg

mainWith :: IO [String] -> IO (Raw, String) -> IO ()
mainWith getOpt getRaw = do
  getOpt >>= \case
    ["nf"]   -> do
      (t, file) <- getRaw
      case infer (emptyCtx (initialPos file)) t of
        Left err -> displayError file err
        Right (t, a) -> do
          print $ nf emptyEnv a t
          putStrLn "  :"
          print $ quote emptyEnv VU a
    ["type"] -> do
      (t, file) <- getRaw
      case infer (emptyCtx (initialPos file)) t of
        Left err     -> displayError file err
        Right (t, a) -> print $ quote emptyEnv a VU
    _ -> putStrLn "unknown option"

main :: IO ()
main = mainWith getArgs parseStdin

main' :: String -> String -> IO ()
main' mode src = mainWith (pure [mode]) ((,src) <$> parseString src)

mainFile :: String -> String -> IO ()
mainFile mode fn = mainWith (pure [mode]) (parseFile fn)
