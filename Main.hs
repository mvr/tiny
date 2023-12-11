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

  ---- Cubical:
  | RTiny0 | RTiny1
  | RPath Raw Raw
  -- RLam and RApp are reused for paths
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

  ---- Cubical:
  | Tiny0 | Tiny1
  | Path Name Ty Tm Tm
  | PLam Name Tm Tm Tm
  | PApp Tm Tm Tm Tm

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
      . showsPrec 11 (fenv (VNeutral (NVar (Lvl $ 1000) [])))

-- Just derive this
instance Functor EnvVars where
  fmap f EnvEmpty = EnvEmpty
  fmap f (EnvVal v env) = EnvVal (f v) (fmap f env)
  fmap f (EnvLock fenv) = EnvLock (\v -> fmap f (fenv v))

makeVarLvl :: Lvl -> Val
makeVarLvl lvl = VNeutral (NVar lvl [])

makeVar :: Env v -> Val
makeVar env = makeVarLvl (Lvl $ envLength env)

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
  = VNeutral Neutral
  | VU
  | VPi Name VTy Closure
  | VLam Name Closure
  | VSg Name VTy Closure
  | VPair Val Val

  ---- New:
  | VTiny
  | VRoot LockName RootClosure
  | VRootIntro LockName RootClosure

  ---- Cubical:
  | VTiny0 | VTiny1
  | VPath Name Closure {-a0-} Val {-a1-} Val
  | VPLam Name Closure {-a0-} Val {-a1-} Val
  deriving (Show)

data Neutral
  = NVar Lvl [Val]
  | NApp Neutral Val
  | NFst Neutral
  | NSnd Neutral

  ---- New:
  | NRootElim (BindTiny Neutral)

  ---- Cubical:
  | NPApp {-p-} Neutral {-t-} Val {-a0-} Val {-a1-} Val
  deriving (Show)

data Normal = Normal {nfTy :: VTy, nfTerm :: Val}
  deriving (Show)

class Apply a b c | a -> b c where
  apply :: Lvl -> a -> b -> c

instance Apply Closure Val Val where
  apply fr (Closure cloenv t) u =
    let newEnv = (extVal cloenv u) { envFresh = max (envFresh cloenv) fr } in
      eval newEnv t

instance (Renameable a) => Apply (BindTiny a) Lvl a where
  apply fr (BindTiny l i a) j
    | i == j    = a
    | otherwise = rename fr j i a

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
    VNeutral n -> VNeutral (addKeys fr ks n)
    VU -> VU
    VPi x a b -> VPi x (addKeys fr ks a) (addKeys fr ks b)
    VLam x c -> VLam x (addKeys fr ks c)
    VSg x a b -> VSg x (addKeys fr ks a) (addKeys fr ks b)
    VPair x y -> VPair (addKeys fr ks x) (addKeys fr ks y)
    VTiny -> VTiny
    VRoot l c -> VRoot l (addKeys fr ks c)
    VRootIntro l c -> VRootIntro l (addKeys fr ks c)
    VTiny0 -> VTiny0
    VTiny1 -> VTiny1
    VPath l c a0 a1 -> VPath l (addKeys fr ks c) (addKeys fr ks a0) (addKeys fr ks a1)
    VPLam l c a0 a1 -> VPLam l (addKeys fr ks c) (addKeys fr ks a0) (addKeys fr ks a1)

instance Keyable Neutral where
  addKeys fr ks = \case
    NVar lvl keys -> NVar lvl (ks ++ fmap (addKeys fr ks) keys)
    NApp f a -> NApp (addKeys fr ks f) (addKeys fr ks a)
    NFst a -> NFst (addKeys fr ks a)
    NSnd a -> NSnd (addKeys fr ks a)
    NRootElim bt -> NRootElim (addKeys fr ks bt)
    NPApp p i a0 a1 -> NPApp (addKeys fr ks p) (addKeys fr ks i) (addKeys fr ks a0) (addKeys fr ks a1)

instance Keyable Normal where
  addKeys fr ks (Normal ty a) = Normal (addKeys fr ks ty) (addKeys fr ks a)

instance Keyable Closure where
  addKeys fr ks (Closure env t) = Closure (addKeys fr ks env) t

instance Keyable RootClosure where
  addKeys fr ks (RootClosure env t) = RootClosure (addKeys fr ks env) t

instance (Keyable a, Renameable a) => Keyable (BindTiny a) where
  addKeys fr ks bt@(BindTiny l lvl n) = BindTiny l fr (addKeys (fr+1) ks (apply (fr+1) bt fr))

instance Keyable v => Keyable (EnvVars v) where
  addKeys fr ks EnvEmpty = EnvEmpty
  addKeys fr ks (EnvVal v env) = EnvVal (addKeys fr ks v) (addKeys fr ks env)
  addKeys fr ks (EnvLock f) = EnvLock (addKeys fr ks . f)

instance Keyable v => Keyable (Env v) where
  addKeys fr ks env = env { envFresh = max (envFresh env) fr,
                            envVars = addKeys fr ks (envVars env) }

-- Substitutes a value for a variable
-- This may cause reduction
-- so Neutral -> Val and Normal -> Val
class Substitutable a b | a -> b where
  sub :: Lvl -> Val -> Lvl -> a -> b

instance Substitutable Val Val where
  sub fr v i = \case
    VNeutral n -> sub fr v i n
    VU -> VU
    VPi x a b -> VPi x (sub fr v i a) (sub fr v i b)
    VLam x c -> VLam x (sub fr v i c)
    VSg x a b -> VSg x (sub fr v i a) (sub fr v i b)
    VPair a b -> VPair (sub fr v i a) (sub fr v i b)
    VTiny -> VTiny
    VRoot l c -> VRoot l (sub fr v i c)
    VRootIntro l c -> VRootIntro l (sub fr v i c)
    VTiny0 -> VTiny0
    VTiny1 -> VTiny1
    VPath l c a0 a1 -> VPath l (sub fr v i c) (sub fr v i a0) (sub fr v i a1)
    VPLam l c a0 a1 -> VPLam l (sub fr v i c) (sub fr v i a0) (sub fr v i a1)

instance Substitutable Neutral Val where
  sub fr v i = \case
    var@(NVar j ks) | i == j -> addKeys fr (fmap (sub fr v i) ks) v
                    | otherwise -> VNeutral (NVar j (fmap (sub fr v i) ks))
    NApp f a -> apply fr (sub fr v i f) (sub fr v i a)
    NFst a -> doFst (sub fr v i a)
    NSnd b -> doSnd fr (sub fr v i b)
    NRootElim bt -> doRootElim (fr+1) (sub (fr+1) v i freshened) fr
      where freshened = apply (fr+1) bt fr
    NPApp p t a0 a1 -> doPApp fr (sub fr v i p) (sub fr v i t) (sub fr v i a0) (sub fr v i a1)

instance Substitutable Normal Val where
  sub fr v i (Normal ty a) = sub fr v i a

instance Substitutable Closure Closure where
  sub fr v i (Closure env t) = Closure (sub fr v i env) t

instance Substitutable RootClosure RootClosure where
  sub fr v i (RootClosure env t) = RootClosure (sub fr v i env) t

instance Substitutable (BindTiny Neutral) (BindTiny Val) where
  sub fr v i bt@(BindTiny l lvl n) = BindTiny l fr (sub (fr+1) v i (apply (fr+1) bt fr))

-- instance Substitutable v v' => Substitutable (Env v) (Env v') where
instance Substitutable (EnvVars Val) (EnvVars Val) where
  sub fr v i EnvEmpty = EnvEmpty
  sub fr v i (EnvVal e env) = EnvVal (sub fr v i e) (sub fr v i env)
  sub fr v i (EnvLock f) = EnvLock (sub fr v i . f)

instance Substitutable (Env Val) (Env Val) where
  sub fr v i env = env { envFresh = max (envFresh env) fr,
                         envVars  = sub fr v i (envVars env) }

-- Switch one de Bruijn level for another
-- The variables have the same types,
-- so this cannot cause reduction
class Renameable a where
  rename :: Lvl -> Lvl -> Lvl -> a -> a

instance Renameable Val where
  rename fr v i = \case
    VNeutral n -> VNeutral (rename fr v i n)
    VU -> VU
    VPi x a b -> VPi x (rename fr v i a) (rename fr v i b)
    VLam x c -> VLam x (rename fr v i c)
    VSg x a b -> VSg x (rename fr v i a) (rename fr v i b)
    VPair a b -> VPair (rename fr v i a) (rename fr v i b)
    VTiny -> VTiny
    VRoot l c -> VRoot l (rename fr v i c)
    VRootIntro l c -> VRootIntro l (rename fr v i c)
    VTiny0 -> VTiny0
    VTiny1 -> VTiny1
    VPath l c a0 a1 -> VPath l (rename fr v i c) (rename fr v i a0) (rename fr v i a1)
    VPLam l c a0 a1 -> VPLam l (rename fr v i c) (rename fr v i a0) (rename fr v i a1)

instance Renameable Neutral where
  rename fr v i = \case
    NVar j ks | i == j -> NVar v (fmap (rename fr v i) ks)
              | otherwise -> NVar j (fmap (rename fr v i) ks)
    NApp f a -> NApp (rename fr v i f) (rename fr v i a)
    NFst a -> NFst (rename fr v i a)
    NSnd a -> NSnd (rename fr v i a)
    NRootElim bt -> NRootElim (rename fr v i bt)
    NPApp p i' a0 a1 -> NPApp (rename fr v i p) (rename fr v i i') (rename fr v i a0) (rename fr v i a1)

instance Renameable Normal where
  rename fr v i (Normal ty a) = Normal (rename fr v i ty) (rename fr v i a)

instance Renameable Closure where
  rename fr v i (Closure env t) = Closure (rename fr v i env) t

instance Renameable RootClosure where
  rename fr v i (RootClosure env t) = RootClosure (rename fr v i env) t

instance Renameable a => Renameable (BindTiny a) where
  rename fr v i bt@(BindTiny l j a)
    | v == j = BindTiny l fr (rename (fr+1) v i (apply (fr+1) bt fr))
    | otherwise = BindTiny l j (rename fr v i a)

instance Renameable v => Renameable (EnvVars v) where
  rename fr v i EnvEmpty = EnvEmpty
  rename fr v i (EnvVal e env) = EnvVal (rename fr v i e) (rename fr v i env)
  rename fr v i (EnvLock f) = EnvLock (rename fr v i . f)

instance Renameable (Env Val) where
  rename fr v i env = env {
    envFresh = max (envFresh env) fr,
    envVars = rename fr v i (envVars env)
    }

-- evaluation
------------------------------------------------------------

doApp :: Lvl -> Val -> Val -> Val
doApp fr (VLam _ t) u = apply fr t u
doApp fr (VNeutral ne) a = VNeutral (NApp ne a)
doApp fr t u = error $ "Unexpected in App: " ++ show t ++ " applied to " ++ show u

instance Apply Val Val Val where
  apply = doApp

doFst :: Val -> Val
doFst (VPair a b) = a
doFst (VNeutral ne) = VNeutral (NFst ne)
doFst t = error $ "Unexpected in fst: " ++ show t

doSnd :: Lvl -> Val -> Val
doSnd fr (VPair a b) = b
doSnd fr (VNeutral ne) = VNeutral (NSnd ne)
doSnd fr t = error $ "Unexpected in snd: " ++ show t

doRootElim :: Lvl -> Val -> Lvl -> Val
doRootElim fr (VRootIntro l c) lvl = coapply fr c lvl
doRootElim fr (VNeutral ne) lvl = VNeutral (NRootElim (BindTiny "geni" lvl ne))
doRootElim fr v lvl = error $ "Unexpected in relim: " ++ show v

instance CoApply Val Lvl Val where
  coapply = doRootElim

doRootElimEta :: Env v -> Val -> Val
doRootElimEta env r =
  let lvl = envFresh env
  in doRootElim (lvl + 1) (addKey (lvl+1) (makeVarLvl lvl) r) lvl

doPApp :: Lvl -> Val -> Val -> Val -> Val -> Val
doPApp fr p VTiny0 a0 a1 = a0
doPApp fr p VTiny1 a0 a1 = a1
doPApp fr (VPLam x c _ _) t a0 a1 = apply fr c t
doPApp fr (VNeutral ne) t a0 a1 = VNeutral (NPApp ne t a0 a1)
doPApp fr v _ _ _ = error $ "Unexpected in papp: " ++ show v

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
  RootElim x t                -> let lvl = envFresh env in coapply (1+lvl) (eval (env `extVal` makeVarLvl lvl) t) lvl

  Tiny0 -> VTiny0
  Tiny1 -> VTiny1
  Path x a a0 a1 -> VPath x (Closure env a) (eval env a0) (eval env a1)
  PLam x a a0 a1 -> VPLam x (Closure env a) (eval env a0) (eval env a1)
  PApp p t a0 a1 -> doPApp (envFresh env) (eval env p) (eval env t) (eval env a0) (eval env a1)

quote :: Env Val -> Val -> Tm
quote env = \case
  VU                           -> U
  VPi x a b                    -> Pi x (quote env a) (let var = makeVar env in quote (env `extVal` var) (apply (1+envFresh env) b var))
  VSg x a b                    -> Sg x (quote env a) (let var = makeVar env in quote (env `extVal` var) (apply (1+envFresh env) b var))

  ---- New:
  VTiny                        -> Tiny
  VRoot l a                    -> Root l (quote (extStuck env) (appRootClosureStuck a))

  VPath x a a0 a1              -> Path x (let var = makeVar env in quote (env `extVal` var) (apply (1+envFresh env) a var)) (quote env a0) (quote env a1)

  (VLam x c)         -> Lam x (let var = makeVar env in quote (env `extVal` var) (apply (1+envFresh env) c var))

  (VPair fst snd)    -> Pair (quote env fst) (quote env snd)

  ---- New:
  (VRootIntro l c)   -> RootIntro l (quote (extStuck env) (appRootClosureStuck c))


  VTiny0                       -> Tiny0
  VTiny1                       -> Tiny1
  (VPLam x p a0 a1)            ->
     let var = makeVar env
     in PLam x (quote (env `extVal` var) (apply (1+envFresh env) p var)) (quote env a0) (quote env a1)

  (VNeutral ne)              -> quoteNeutral env ne

  v                          -> error $ "Can't quote " ++ show v

quoteNeutral :: Env Val -> Neutral -> Tm
quoteNeutral env (NVar x keys) = Var (lvl2Ix env x) (fmap (quote env) keys)
quoteNeutral env (NApp f a) = App (quoteNeutral env f) (quote env a)
quoteNeutral env (NFst a) = Fst (quoteNeutral env a)
quoteNeutral env (NSnd a) = Snd (quoteNeutral env a)
quoteNeutral env (NRootElim bt@(BindTiny l lvl r)) = RootElim l (let lvl = envFresh env in quoteNeutral (env `extVal` makeVarLvl lvl) (apply (1+lvl) bt lvl))
quoteNeutral env (NPApp p t a0 a1) = PApp (quoteNeutral env p) (quote env t) (quote env a0) (quote env a1)

nf :: Env Val -> VTy -> Tm -> Tm
nf env a t = quote env (eval env t)

-- conversion
------------------------------------------------------------

eq :: Env Val -> Val -> Val -> Bool
-- eq env p1 p2 | traceShow ("eq:", p1, p2) False = undefined
eq env VU VU =True
eq env (VNeutral ne1) (VNeutral ne2) = eqNE env ne1 ne2
eq env (VPi _ aty1 bclo1) (VPi _ aty2 bclo2) =
  let var = makeVar env
   in eq env aty1 aty2
        && eq (env `extVal` var) (apply (1+envFresh env) bclo1 var) (apply (1+envFresh env) bclo2 var)
eq env (VSg _ aty1 bclo1) (VSg _ aty2 bclo2) =
  let var = makeVar env
   in eq env aty1 aty2
        && eq (env `extVal` var) (apply (1+envFresh env) bclo1 var) (apply (1+envFresh env) bclo2 var)
eq env VTiny VTiny = True
eq env (VRoot _ a) (VRoot _ a') = eq (extStuck env) (appRootClosureStuck a) (appRootClosureStuck a')
eq env (VPath _ c a0 a1) (VPath _ c' a0' a1') =
  let var = makeVar env
   in eq (env `extVal` var) (apply (1+envFresh env) c var) (apply (1+envFresh env) c' var)
      && eq env a0 a0'
      && eq env a1 a1'

eq env (VLam x b) (VLam x' b') =
  let var = makeVar env
  in eq (env `extVal` var) (apply (1 + envFresh env) b var) (apply (1 + envFresh env) b' var)
eq env (VLam x b) f' =
  let var = makeVar env
  in eq (env `extVal` var) (apply (1 + envFresh env) b var) (apply (1 + envFresh env) f' var)
eq env f (VLam x' b')  =
  let var = makeVar env
  in eq (env `extVal` var) (apply (1 + envFresh env) f var) (apply (1 + envFresh env) b' var)

eq env (VPair a1 b1) (VPair a2 b2) =
  eq env a1 a2 && eq env b1 b2
eq env (VPair a1 b1) p2 =
  eq env a1 (doFst p2) && eq env b1 (doSnd (envFresh env) p2)
eq env p1 (VPair a2 b2) =
  eq env (doFst p1) a2 && eq env (doSnd (envFresh env) p1) b2

eq env (VRootIntro l a1) (VRootIntro _ a2) =
  eq (extStuck env) (appRootClosureStuck a1) (appRootClosureStuck a2)
eq env (VRootIntro l a1) r2 =
  eq (extStuck env) (appRootClosureStuck a1) (doRootElimEta env r2)
eq env r1 (VRootIntro l a2) =
  eq (extStuck env) (doRootElimEta env r1) (appRootClosureStuck a2)

eq env (VPLam x b a0 a1) (VPLam x' b' _ _) =
  let var = makeVar env
  in eq (env `extVal` var) (apply (1 + envFresh env) b var) (apply (1 + envFresh env) b' var)
eq env (VPLam x b a0 a1) f' =
  let var = makeVar env
  in eq (env `extVal` var) (apply (1 + envFresh env) b var) (doPApp (1 + envFresh env) f' var a0 a1)
eq env f (VPLam x' b' a0 a1)  =
  let var = makeVar env
  in eq (env `extVal` var) (doPApp (1 + envFresh env) f var a0 a1) (apply (1 + envFresh env) b' var)
eq _ _ _ = False

eqNE :: Env Val -> Neutral -> Neutral -> Bool
-- eqNE env p1 p2 | traceShow ("eqNE:", p1, p2) False = undefined
eqNE env (NVar i ikeys) (NVar j jkeys) = i == j && all (uncurry keyeq) (zip ikeys jkeys)
  where keyeq ik jk = eq env ik jk
eqNE env (NApp f1 a1) (NApp f2 a2) =
  eqNE env f1 f2 && eq env a1 a2
eqNE env (NFst p1) (NFst p2) = eqNE env p1 p2
eqNE env (NSnd p1) (NSnd p2) = eqNE env p1 p2
eqNE env (NRootElim tb1) (NRootElim tb2) = eqNE (env `extVal` var) (apply (1 + envFresh env) tb1 lvl) (apply (1 + envFresh env) tb2 lvl)
  where lvl = envFresh env
        var = makeVarLvl lvl
eqNE env (NPApp f1 a1 _ _) (NPApp f2 a2 _ _) =
  eqNE env f1 f2 && eq env a1 a2
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
bind x a ctx = define x (makeVar (env ctx)) a ctx

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
    Lam x <$> check (bind x a ctx) t (apply (1 + Lvl (ctxLength ctx)) b (makeVar (env ctx)))

  (RPair a b, VSg x aty bty) -> do
    a <- check ctx a aty
    b <- check ctx b (apply (1 + Lvl (ctxLength ctx)) bty (eval (ctxVals ctx) a))
    pure (Pair a b)

  ---- New:

  (RRootIntro x t, VRoot x' a)
    -> RootIntro x <$> check (bindStuckLock x ctx) t (appRootClosureStuck a)

  (RLam x t, VPath x' c a0 a1) -> do
    t <- check (bind x VTiny ctx) t (apply (1 + Lvl (ctxLength ctx)) c (makeVar (env ctx)))
    unless (eq (ctxVals ctx) a0 (eval (ctxVals ctx `extVal` VTiny0) t)
         && eq (ctxVals ctx) a1 (eval (ctxVals ctx `extVal` VTiny1) t)) $
      report ctx "endpoint mismatch: "

    pure $ PLam x t (quote (ctxVals ctx) a0) (quote (ctxVals ctx) a1)

  _ -> do
    (t, tty) <- infer ctx t
    unless (eq (ctxVals ctx) tty a) $
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

  RTiny0 -> pure (Tiny0, VTiny)
  RTiny1 -> pure (Tiny1, VTiny)

  RPath a b -> do
    (a, aty) <- infer ctx a
    b <- check ctx b aty
    pure (Path "_" (quote (ctxVals ctx `extVal` makeVar (ctxVals ctx)) aty) a b, VU)

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

    Tiny0                     -> ("0"++)
    Tiny1                     -> ("1"++)

    Path (fresh ns -> x) a a0 a1 -> ("PathP ("++) . (x++) . (". "++) . go pip (x:ns) a . (") "++) . go atomp ns a0 . (' ':) . go atomp ns a1
    PLam (fresh ns -> x) t a0 a1 -> par p letp $ ("λ "++) . (x++) . (". "++) . go letp (x:ns) t
    PApp t u a0 a1               -> par p appp $ go appp ns t . (' ':) . go atomp ns u

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
keyword x = x == "let" || x == "in" || x == "λ" || x == "U" || x == "T" || x == "rintro" || x == "relim" || x == "fst" || x == "snd" || x == "Path"

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
      withPos (pVar <|> (RU <$ symbol "U") <|> (RTiny <$ symbol "T") <|> (RTiny0 <$ symbol "0") <|> (RTiny1 <$ symbol "1"))
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

pPath = do
  symbol "Path"
  a0 <- pAtom
  a1 <- pAtom
  pure (RPath a0 a1)

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
  symbol ":="
  t <- pRaw
  symbol ";"
  u <- pRaw
  pure $ RLet x a t u

pRaw = withPos (pLam <|> pPair <|> pFst <|> pSnd <|> pLet <|> pRoot <|> pRootIntro <|> pRootElim <|> pPath <|> try pPi <|> try pSg <|> funOrSpine)
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
  pure (tm, file)

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
          print $ quote emptyEnv a
    ["type"] -> do
      (t, file) <- getRaw
      case infer (emptyCtx (initialPos file)) t of
        Left err     -> displayError file err
        Right (t, a) -> print $ quote emptyEnv a
    _ -> putStrLn "unknown option"

main :: IO ()
main = mainWith getArgs parseStdin

main' :: String -> String -> IO ()
main' mode src = mainWith (pure [mode]) ((,src) <$> parseString src)

mainFile :: String -> String -> IO ()
mainFile mode fn = mainWith (pure [mode]) (parseFile fn)
