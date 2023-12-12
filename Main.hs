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

type FreshArg = (?fresh :: Lvl)

freshLvl :: (FreshArg => Lvl -> a) -> (FreshArg => a)
freshLvl act = let v = ?fresh in let ?fresh = ?fresh + 1 in seq ?fresh (act v)

fresh :: (FreshArg => Val -> a) -> (FreshArg => a)
fresh act = let v = VNeutral (NVar ?fresh []) in let ?fresh = ?fresh + 1 in seq ?fresh (act v)

type Name = String

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
  | RRoot Raw
  | RRootIntro Raw
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
  | Root Ty
  | RootIntro Tm
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

type EnvArg v = (?env :: Env v)

makeVarLvl :: Lvl -> Val
makeVarLvl lvl = VNeutral (NVar lvl [])

makeVar :: Env v -> Val
makeVar env = makeVarLvl (Lvl $ envLength env)

lvl2Ix :: Env v -> Lvl -> Ix
lvl2Ix env (Lvl x) = Ix (envLength env - x - 1)

ix2Lvl :: Env v -> Ix -> Lvl
ix2Lvl env (Ix x) = Lvl (envLength env - x - 1)

define :: v -> (FreshArg => EnvArg v => a) -> (FreshArg => EnvArg v => a)
define v act = let ?env = ?env { envVars = EnvVal v (envVars ?env),
                                 envLength = 1 + envLength ?env,
                                 envFresh = 1 + envFresh ?env }
                   ?fresh = ?fresh + 1
               in act

defineUnit :: Lvl -> (FreshArg => EnvArg Val => a) -> (FreshArg => EnvArg Val => a)
defineUnit lvl act = let ?env = ?env { envVars = EnvLock (\v -> sub v lvl (envVars ?env)),
                                       envLength = 1 + envLength ?env,
                                       envFresh = 1 + envFresh ?env }
                         ?fresh = ?fresh + 1
                     in act

defineStuck :: Keyable v => (FreshArg => EnvArg v => a) -> (FreshArg => EnvArg v => a)
defineStuck act = let ?env = ?env { envVars = EnvLock (\v -> addKey v (envVars ?env)),
                                    envLength = 1 + envLength ?env,
                                    envFresh = 1 + envFresh ?env }
                      ?fresh = ?fresh + 1
                  in act

-- Note: giving they type of lvl is necessary (with
-- NoMonomorphismRestriction), otherwise it has type
-- (?env :: EnvArg Val) => Int and so is incremented
-- in (act v)

nextVar :: (FreshArg => EnvArg Val => Val -> a) -> (FreshArg => EnvArg Val => a)
nextVar act = let lvl :: Int
                  lvl = envLength ?env in
              let v = VNeutral (NVar (Lvl lvl) []) in
              define v (act v)

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
  | VRoot RootClosure
  | VRootIntro RootClosure

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
  apply :: FreshArg  => a -> b -> c

instance Apply Closure Val Val where
  apply (Closure cloenv t) u =
    let ?env = cloenv { envFresh = max (envFresh cloenv) ?fresh }
    in define u (eval t)

instance (Renameable a) => Apply (BindTiny a) Lvl a where
  apply (BindTiny l i a) j
    | i == j    = a
    | otherwise = rename j i a

class CoApply a b c | a -> b c where
  coapply :: FreshArg => a -> b -> c

instance CoApply RootClosure Lvl Val where
  coapply (RootClosure cloenv t) lvl =
    let ?env = cloenv { envFresh = max (envFresh cloenv) ?fresh }
    in defineUnit lvl (eval t)

appRootClosureStuck :: FreshArg => EnvArg Val => RootClosure -> Val
appRootClosureStuck (RootClosure cloenv t) =
  let ?env = cloenv { envFresh = max (envFresh cloenv) ?fresh }
  in defineStuck (eval t)

-- substitutions
------------------------------------------------------------

-- TODO: "NVar and EnvLock are the only interesting cases" is this true?

-- Appends keys to all free variables
-- This cannot cause reduction
class Keyable a where
  addKeys :: FreshArg => [Val] -> a -> a
  addKey :: FreshArg => Val -> a -> a
  addKey k = addKeys [k]

instance Keyable Name where
  addKeys ks n = n

instance (Keyable a, Keyable b) => Keyable (a, b) where
  addKeys ks (a, b) = (addKeys ks a, addKeys ks b)

instance (Keyable a, Keyable b, Keyable c) => Keyable (a, b, c) where
  addKeys ks (a, b, c) = (addKeys ks a, addKeys ks b, addKeys ks c)

instance Keyable Val where
  addKeys ks = \case
    VNeutral n -> VNeutral (addKeys ks n)
    VU -> VU
    VPi x a b -> VPi x (addKeys ks a) (addKeys ks b)
    VLam x c -> VLam x (addKeys ks c)
    VSg x a b -> VSg x (addKeys ks a) (addKeys ks b)
    VPair x y -> VPair (addKeys ks x) (addKeys ks y)
    VTiny -> VTiny
    VRoot c -> VRoot (addKeys ks c)
    VRootIntro c -> VRootIntro (addKeys ks c)
    VTiny0 -> VTiny0
    VTiny1 -> VTiny1
    VPath l c a0 a1 -> VPath l (addKeys ks c) (addKeys ks a0) (addKeys ks a1)
    VPLam l c a0 a1 -> VPLam l (addKeys ks c) (addKeys ks a0) (addKeys ks a1)

instance Keyable Neutral where
  addKeys ks = \case
    NVar lvl keys -> NVar lvl (ks ++ fmap (addKeys ks) keys)
    NApp f a -> NApp (addKeys ks f) (addKeys ks a)
    NFst a -> NFst (addKeys ks a)
    NSnd a -> NSnd (addKeys ks a)
    NRootElim bt -> NRootElim (addKeys ks bt)
    NPApp p i a0 a1 -> NPApp (addKeys ks p) (addKeys ks i) (addKeys ks a0) (addKeys ks a1)

instance Keyable Normal where
  addKeys ks (Normal ty a) = Normal (addKeys ks ty) (addKeys ks a)

instance Keyable Closure where
  addKeys ks (Closure env t) = Closure (addKeys ks env) t

instance Keyable RootClosure where
  addKeys ks (RootClosure env t) = RootClosure (addKeys ks env) t

instance (Keyable a, Renameable a) => Keyable (BindTiny a) where
  addKeys ks bt@(BindTiny l lvl n) = freshLvl $ \fr -> BindTiny l fr (addKeys ks (apply bt fr))

instance Keyable v => Keyable (EnvVars v) where
  addKeys ks EnvEmpty = EnvEmpty
  addKeys ks (EnvVal v env) = EnvVal (addKeys ks v) (addKeys ks env)
  addKeys ks (EnvLock f) = EnvLock (addKeys ks . f)

instance Keyable v => Keyable (Env v) where
  addKeys ks env = env { envFresh = max (envFresh env) ?fresh, envVars = addKeys ks (envVars env) }

-- Substitutes a value for a variable
-- This may cause reduction
-- so Neutral -> Val and Normal -> Val
class Substitutable a b | a -> b where
  sub :: FreshArg => Val -> Lvl -> a -> b

instance Substitutable Val Val where
  sub v i = \case
    VNeutral n -> sub v i n
    VU -> VU
    VPi x a b -> VPi x (sub v i a) (sub v i b)
    VLam x c -> VLam x (sub v i c)
    VSg x a b -> VSg x (sub v i a) (sub v i b)
    VPair a b -> VPair (sub v i a) (sub v i b)
    VTiny -> VTiny
    VRoot c -> VRoot (sub v i c)
    VRootIntro c -> VRootIntro (sub v i c)
    VTiny0 -> VTiny0
    VTiny1 -> VTiny1
    VPath l c a0 a1 -> VPath l (sub v i c) (sub v i a0) (sub v i a1)
    VPLam l c a0 a1 -> VPLam l (sub v i c) (sub v i a0) (sub v i a1)

instance Substitutable Neutral Val where
  sub v i = \case
    var@(NVar j ks) | i == j -> addKeys (fmap (sub v i) ks) v
                    | otherwise -> VNeutral (NVar j (fmap (sub v i) ks))
    NApp f a -> apply (sub v i f) (sub v i a)
    NFst a -> doFst (sub v i a)
    NSnd b -> doSnd (sub v i b)
    NRootElim bt -> freshLvl $ \fr -> doRootElim (sub v i (apply bt fr)) fr
    NPApp p t a0 a1 -> doPApp (sub v i p) (sub v i t) (sub v i a0) (sub v i a1)

instance Substitutable Normal Val where
  sub v i (Normal ty a) = sub v i a

instance Substitutable Closure Closure where
  sub v i (Closure env t) = Closure (sub v i env) t

instance Substitutable RootClosure RootClosure where
  sub v i (RootClosure env t) = RootClosure (sub v i env) t

instance Substitutable (BindTiny Neutral) (BindTiny Val) where
  sub v i bt@(BindTiny l lvl n) = freshLvl $ \fr -> BindTiny l fr (sub v i (apply bt fr))

-- instance Substitutable v v' => Substitutable (Env v) (Env v') where
instance Substitutable (EnvVars Val) (EnvVars Val) where
  sub v i EnvEmpty = EnvEmpty
  sub v i (EnvVal e env) = EnvVal (sub v i e) (sub v i env)
  sub v i (EnvLock f) = EnvLock (sub v i . f)

instance Substitutable (Env Val) (Env Val) where
  sub v i env = env { envFresh = max (envFresh env) ?fresh, envVars  = sub v i (envVars env) }

-- Switch one de Bruijn level for another
-- The variables have the same types,
-- so this cannot cause reduction
class Renameable a where
  rename :: FreshArg => Lvl -> Lvl -> a -> a

instance Renameable Val where
  rename v i = \case
    VNeutral n -> VNeutral (rename v i n)
    VU -> VU
    VPi x a b -> VPi x (rename v i a) (rename v i b)
    VLam x c -> VLam x (rename v i c)
    VSg x a b -> VSg x (rename v i a) (rename v i b)
    VPair a b -> VPair (rename v i a) (rename v i b)
    VTiny -> VTiny
    VRoot c -> VRoot (rename v i c)
    VRootIntro c -> VRootIntro (rename v i c)
    VTiny0 -> VTiny0
    VTiny1 -> VTiny1
    VPath l c a0 a1 -> VPath l (rename v i c) (rename v i a0) (rename v i a1)
    VPLam l c a0 a1 -> VPLam l (rename v i c) (rename v i a0) (rename v i a1)

instance Renameable Neutral where
  rename v i = \case
    NVar j ks | i == j -> NVar v (fmap (rename v i) ks)
              | otherwise -> NVar j (fmap (rename v i) ks)
    NApp f a -> NApp (rename v i f) (rename v i a)
    NFst a -> NFst (rename v i a)
    NSnd a -> NSnd (rename v i a)
    NRootElim bt -> NRootElim (rename v i bt)
    NPApp p i' a0 a1 -> NPApp (rename v i p) (rename v i i') (rename v i a0) (rename v i a1)

instance Renameable Normal where
  rename v i (Normal ty a) = Normal (rename v i ty) (rename v i a)

instance Renameable Closure where
  rename v i (Closure env t) = Closure (rename v i env) t

instance Renameable RootClosure where
  rename v i (RootClosure env t) = RootClosure (rename v i env) t

instance Renameable a => Renameable (BindTiny a) where
  rename v i bt@(BindTiny l j a)
    | v == j = freshLvl $ \fr -> BindTiny l fr (rename v i (apply bt fr))
    | otherwise = BindTiny l j (rename v i a)

instance Renameable v => Renameable (EnvVars v) where
  rename v i EnvEmpty = EnvEmpty
  rename v i (EnvVal e env) = EnvVal (rename v i e) (rename v i env)
  rename v i (EnvLock f) = EnvLock (rename v i . f)

instance Renameable (Env Val) where
  rename v i env = env {
    envFresh = max (envFresh env) ?fresh,
    envVars = rename v i (envVars env)
    }

-- evaluation
------------------------------------------------------------

doApp :: FreshArg => Val -> Val -> Val
doApp (VLam _ t) u = apply t u
doApp (VNeutral ne) a = VNeutral (NApp ne a)
doApp t u = error $ "Unexpected in App: " ++ show t ++ " applied to " ++ show u

instance Apply Val Val Val where
  apply = doApp

doFst :: Val -> Val
doFst (VPair a b) = a
doFst (VNeutral ne) = VNeutral (NFst ne)
doFst t = error $ "Unexpected in fst: " ++ show t

doSnd :: Val -> Val
doSnd (VPair a b) = b
doSnd (VNeutral ne) = VNeutral (NSnd ne)
doSnd t = error $ "Unexpected in snd: " ++ show t

doRootElim :: FreshArg => Val -> Lvl -> Val
doRootElim (VRootIntro c) lvl = coapply c lvl
doRootElim (VNeutral ne) lvl = VNeutral (NRootElim (BindTiny "geni" lvl ne))
doRootElim v lvl = error $ "Unexpected in relim: " ++ show v

instance CoApply Val Lvl Val where
  coapply = doRootElim

doRootElimEta :: FreshArg => EnvArg v => Val -> Val
doRootElimEta r = freshLvl $ \fr -> doRootElim (addKey (makeVarLvl fr) r) fr

doPApp :: FreshArg => Val -> Val -> Val -> Val -> Val
doPApp p VTiny0 a0 a1 = a0
doPApp p VTiny1 a0 a1 = a1
doPApp (VPLam x c _ _) t a0 a1 = apply c t
doPApp (VNeutral ne) t a0 a1 = VNeutral (NPApp ne t a0 a1)
doPApp v _ _ _ = error $ "Unexpected in papp: " ++ show v

envLookup :: EnvVars v -> Ix -> [Val] -> v
envLookup env i keys = go i keys env
  where go 0 keys (EnvVal v envtail) = v
        go i keys (EnvVal v envtail) = go (i-1) keys envtail
        go i (k : keys) (EnvLock f) = go (i-1) keys (f k)
        go i [] (EnvLock f) = error "Ran out of keys"
        go _ _ EnvEmpty = error "Ran out of environment"

eval :: FreshArg => EnvArg Val => Tm -> Val
-- eval t = traceShow ("eval", ?env, t) $ case t of
eval t = case t of
  U                           -> VU
  Let x _ t u                 -> define (eval t) (eval u)

  Pi x a b                    -> VPi x (eval a) (Closure ?env b)
  Lam x t                     -> VLam x (Closure ?env t)
  App t u                     -> apply (eval t) (eval u)

  Sg x a b                    -> VSg x (eval a) (Closure ?env b)
  Pair a b                    -> VPair (eval a) (eval b)
  Fst a                       -> doFst (eval a)
  Snd a                       -> doSnd (eval a)

  ---- New:
  Var x keys                  -> envLookup (envVars ?env) x (fmap eval keys)
  Tiny                        -> VTiny
  Root a                      -> VRoot (RootClosure ?env a)
  RootIntro t                 -> VRootIntro (RootClosure ?env t)
  RootElim x t                -> freshLvl $ \fr -> coapply (define (makeVarLvl fr) (eval t)) fr

  Tiny0 -> VTiny0
  Tiny1 -> VTiny1
  Path x a a0 a1 -> VPath x (Closure ?env a) (eval a0) (eval a1)
  PLam x a a0 a1 -> VPLam x (Closure ?env a) (eval a0) (eval a1)
  PApp p t a0 a1 -> doPApp (eval p) (eval t) (eval a0) (eval a1)

quote :: FreshArg => EnvArg Val => Val -> Tm
-- quote v = traceShow ("quote", ?env, v) $ case v of
quote = \case
  VU                           -> U
  VPi x a b                    -> Pi x (quote a) (nextVar \var -> quote (apply b var))
  VSg x a b                    -> Sg x (quote a) (nextVar \var -> quote (apply b var))

  ---- New:
  VTiny                        -> Tiny
  VRoot a                      -> Root (defineStuck (quote (appRootClosureStuck a)))

  VPath x a a0 a1              -> Path x (nextVar \var -> quote (apply a var)) (quote a0) (quote a1)

  (VLam x c)         -> Lam x (nextVar \var -> quote (apply c var))

  (VPair fst snd)    -> Pair (quote fst) (quote snd)

  ---- New:
  (VRootIntro c)   -> RootIntro (defineStuck (quote (appRootClosureStuck c)))


  VTiny0                       -> Tiny0
  VTiny1                       -> Tiny1
  (VPLam x p a0 a1)            -> PLam x (nextVar \var -> quote (apply p var)) (quote a0) (quote a1)

  (VNeutral ne)              -> quoteNeutral ne

  v                          -> error $ "Can't quote " ++ show v

quoteNeutral :: FreshArg => EnvArg Val => Neutral -> Tm
quoteNeutral (NVar x keys) = Var (lvl2Ix ?env x) (fmap quote keys)
quoteNeutral (NApp f a) = App (quoteNeutral f) (quote a)
quoteNeutral (NFst a) = Fst (quoteNeutral a)
quoteNeutral (NSnd a) = Snd (quoteNeutral a)
quoteNeutral (NRootElim bt@(BindTiny l lvl r)) = RootElim l (freshLvl $ \fr -> define (makeVarLvl fr) (quoteNeutral (apply bt fr)))
quoteNeutral (NPApp p t a0 a1) = PApp (quoteNeutral p) (quote t) (quote a0) (quote a1)

nf :: FreshArg => EnvArg Val => Tm -> Tm
nf t = quote (eval t)

-- conversion
------------------------------------------------------------

eq :: FreshArg => EnvArg Val => Val -> Val -> Bool
-- eq p1 p2 | traceShow ("eq:", p1, p2) False = undefined
eq VU VU = True
eq (VNeutral ne1) (VNeutral ne2) = eqNE ne1 ne2
eq (VPi _ aty1 bclo1) (VPi _ aty2 bclo2) = eq aty1 aty2 && nextVar \var -> eq (apply bclo1 var) (apply bclo2 var)
eq (VSg _ aty1 bclo1) (VSg _ aty2 bclo2) = eq aty1 aty2 && nextVar \var -> eq (apply bclo1 var) (apply bclo2 var)
eq VTiny VTiny = True
eq (VRoot a) (VRoot a') = defineStuck $ eq (appRootClosureStuck a) (appRootClosureStuck a')
eq (VPath _ c a0 a1) (VPath _ c' a0' a1') =
  (nextVar \var -> eq (apply c var) (apply c' var))
    && eq a0 a0'
    && eq a1 a1'

eq (VLam x b) (VLam x' b') = nextVar \var -> eq (apply b var) (apply b' var)
eq (VLam x b) f' = nextVar \var -> eq (apply b var) (apply f' var)
eq f (VLam x' b') = nextVar \var -> eq (apply f var) (apply b' var)

eq (VPair a1 b1) (VPair a2 b2) = eq a1 a2 && eq b1 b2
eq (VPair a1 b1) p2 = eq a1 (doFst p2) && eq b1 (doSnd p2)
eq p1 (VPair a2 b2) = eq (doFst p1) a2 && eq (doSnd p1) b2

eq (VRootIntro a1) (VRootIntro a2) = defineStuck $ eq (appRootClosureStuck a1) (appRootClosureStuck a2)
eq (VRootIntro a1) r2 = defineStuck $ eq (appRootClosureStuck a1) (doRootElimEta r2)
eq r1 (VRootIntro a2) = defineStuck $ eq (doRootElimEta r1) (appRootClosureStuck a2)

eq (VPLam x a a0 a1) (VPLam x' a' _ _) = nextVar \var -> eq (apply a var) (apply a' var)
eq (VPLam x a a0 a1) p' = nextVar \var -> eq (apply a var) (apply p' var)
eq p (VPLam x' a' a0 a1) = nextVar \var -> eq (apply p var) (apply a' var)
eq _ _ = False

eqNE :: FreshArg => EnvArg Val => Neutral -> Neutral -> Bool
-- eqNE p1 p2 | traceShow ("eqNE:", p1, p2) False = undefined
eqNE (NVar i ikeys) (NVar j jkeys) = i == j && all (uncurry eq) (zip ikeys jkeys)
eqNE (NApp f1 a1) (NApp f2 a2) = eqNE f1 f2 && eq a1 a2
eqNE (NFst p1) (NFst p2) = eqNE p1 p2
eqNE (NSnd p1) (NSnd p2) = eqNE p1 p2
eqNE (NRootElim tb1) (NRootElim tb2) = freshLvl \fr -> define (makeVarLvl fr) $ eqNE (apply tb1 fr) (apply tb2 fr)
eqNE (NPApp f1 a1 _ _) (NPApp f2 a2 _ _) = eqNE f1 f2 && eq a1 a2
eqNE ne1 ne2 = False

-- type checking
------------------------------------------------------------

-- | Typechecking monad. We annotate the error with the current source position.
type M = Either (String, SourcePos)

data Locals =
  LocalsEmpty
  | LocalsVal Name VTy Locals
  | LocalsLock Locals

type LocalsArg = (?locals :: Locals)

-- | Elaboration context.
-- data Ctx = Ctx {env :: Env (Name, Val, VTy), pos :: SourcePos}
--   deriving (Show)

withEmptyCtx :: SourcePos -> (FreshArg => EnvArg v => LocalsArg => (?pos :: SourcePos) => a) -> a
withEmptyCtx pos a =
  let ?fresh = 0
      ?env = emptyEnv
      ?locals = LocalsEmpty
      ?pos = pos
  in a

ctxDefine :: Name -> v -> VTy -> (FreshArg => EnvArg v => LocalsArg => a) -> (FreshArg => EnvArg v => LocalsArg => a)
ctxDefine x v ty act = define v $ let ?locals = LocalsVal x ty ?locals in act

ctxDefineUnit :: Lvl -> (FreshArg => EnvArg Val => LocalsArg => a) -> (FreshArg => EnvArg Val => LocalsArg => a)
ctxDefineUnit lvl act = defineUnit lvl $ let ?locals = LocalsLock ?locals in act

ctxDefineStuck :: Keyable v => (FreshArg => EnvArg v => LocalsArg => a) -> (FreshArg => EnvArg v => LocalsArg => a)
ctxDefineStuck act = defineStuck $ let ?locals = LocalsLock ?locals in act

ctxNextVar :: Name -> VTy -> (FreshArg => EnvArg Val => LocalsArg => Val -> a) -> (FreshArg => EnvArg Val => LocalsArg => a)
ctxNextVar x ty act =  let ?locals = LocalsVal x ty ?locals in nextVar act

report :: (?pos :: SourcePos) => String -> M a
report msg = Left (msg, ?pos)

check :: FreshArg => EnvArg Val => LocalsArg => (?pos :: SourcePos) =>  Raw -> VTy -> M Tm
check t a = case (t, a) of
-- check t a = traceShow ("check", t, a) $ case (t, a) of
  -- (RSrcPos pos t, a) -> check (ctx {pos = pos}) t a
  (RSrcPos pos t, a) -> let ?pos = pos in check t a

  (RLet x ty t u, a') -> do
    ty <- check ty VU
    let vty = eval ty
    t <- check t vty
    let vt = eval t
    u <- ctxDefine x vt vty $ check u a'
    pure (Let x ty t u)

  (RLam x t, VPi x' a b) ->
    Lam x <$> ctxNextVar x a (\var -> check t (apply b var))

  (RPair a b, VSg x aty bty) -> do
    a <- check a aty
    b <- check b (apply bty (eval a))
    pure (Pair a b)

  ---- New:

  (RRootIntro t, VRoot a)
    -> RootIntro <$> ctxDefineStuck (check t (appRootClosureStuck a))

  (RLam x t, VPath x' c a0 a1) -> do
    t <- ctxNextVar x VTiny (\var -> check t (apply c var))
    unless (eq a0 (define VTiny0 (eval t))
         && eq a1 (define VTiny1 (eval t))) $
      report "endpoint mismatch: "

    pure $ PLam x t (quote a0) (quote a1)

  _ -> do
    (t, tty) <- infer t
    unless (eq tty a) $
     report ("type mismatch: " ++ show tty  ++ ", " ++ show a)
    pure t

infer :: FreshArg => EnvArg Val => LocalsArg => (?pos :: SourcePos) =>  Raw -> M (Tm, VTy)
infer r = case r of
-- infer r = traceShow ("infer", r) $ case r of
-- infer ctx r = traceShow (ctx, r) $ case r of
  RSrcPos pos t -> let ?pos = pos in infer t

  RU -> pure (U, VU)   -- U : U rule

  RLet x a t u -> do
    a <- check a VU
    let va = eval a
    t <- check t va
    let vt = eval t
    (u, uty) <- ctxDefine x vt va $ infer u
    pure (Let x a t u, uty)

  RPi x a b -> do
    a <- check a VU
    b <- ctxNextVar x (eval a) $ \var -> check b VU
    pure (Pi x a b, VU)

  RApp t u -> do
    (t, tty) <- infer t
    case tty of
      VPi _ a b -> do
        u <- check u a
        pure (App t u, apply b (eval u))
      tty ->
        report $ "Expected a function type, instead inferred:\n\n  " ++ "todo" -- showVal ctx tty

  RLam{} -> report "Can't infer type for lambda expression"

  RSg x a b -> do
    a <- check a VU
    b <- ctxNextVar x (eval a) $ \var -> check b VU
    pure (Sg x a b, VU)

  RPair{} -> report "Can't infer type for pair"

  RFst p -> do
    (t, ty) <- infer p
    case ty of
      VSg x a b -> pure (Fst t, a)
      _ -> report "expected Sg type"

  RSnd p -> do
    (t, ty) <- infer p
    case ty of
      VSg x a b -> pure (Snd t, apply b (eval (Fst t)))
      _ -> report "expected Sg type"

  ---- New:
  RVar x rkeys -> do
    let go i EnvEmpty LocalsEmpty _ = report ("variable out of scope: " ++ x)
        go i (EnvVal v env) (LocalsVal x' ty locals) keys
          | x == x'   = case keys of
                          [] -> do
                            keyst <- mapM (\key -> check key VTiny) rkeys
                            pure (Var i keyst, ty)
                          _  -> report ("too many keys provided: " ++ x)
          | otherwise = go (i + 1) env locals keys
        go i (EnvLock env) (LocalsLock locals) [] = report ("not enough keys provided: " ++ x)
        go i (EnvLock fenv) (LocalsLock locals) (key:keys) = do
          keyt <- check key VTiny
          let keyv = eval keyt
          go (i+1) (fenv keyv) locals keys
        go i _ _ _ = error "impossible"
    go 0 (envVars ?env) ?locals rkeys

  RTiny -> pure (Tiny, VU)

  RRoot a -> do
    a <- ctxDefineStuck $ check a VU
    pure (Root a, VU)

  RRootElim x t -> do
    (t, tty) <- ctxNextVar x VTiny $ \var -> infer t
    case tty of
      VRoot c -> do
          pure (RootElim x t, coapply c (Lvl $ envLength ?env))
      tty ->
        report $ "Expected a root type, instead inferred:\n\n  " ++ "todo" -- showVal ctx tty

  RRootIntro{} -> report "Can't infer type for rintro expression"

  RTiny0 -> pure (Tiny0, VTiny)
  RTiny1 -> pure (Tiny1, VTiny)

  RPath a0 a1 -> do
    (a0, aty) <- infer a0
    a1 <- check a1 aty
    pure (Path "_" (ctxNextVar "_" VTiny $ \var -> quote aty) a0 a1, VU)

-- printing
--------------------------------------------------------------------------------

freshName :: [Name] -> Name -> Name
freshName ns "_" = "_"
freshName ns x | elem x ns = freshName ns (x ++ "'")
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

    Let (freshName ns -> x) a t u -> par p letp $ ("let "++) . (x++) . (" : "++) . go letp ns a
                                 . ("\n    = "++) . go letp ns t . ("\nin\n"++) . go letp (x:ns) u

    Pi "_" a b                -> par p pip $ go appp ns a . (" → "++) . go pip ("_":ns) b

    Pi (freshName ns -> x) a b    -> par p pip $ piBind ns x a . goPi (x:ns) b where
                                   goPi ns (Pi "_" a b) =
                                     (" → "++) . go appp ns a . (" → "++) . go pip ("_":ns) b
                                   goPi ns (Pi (freshName ns -> x) a b) =
                                     piBind ns x a . goPi (x:ns) b
                                   goPi ns b =
                                     (" → "++) . go pip ns b

    Lam (freshName ns -> x) t     -> par p letp $ ("λ "++) . (x++) . goLam (x:ns) t where
                                   goLam ns (Lam (freshName ns -> x) t) =
                                     (' ':) . (x++) . goLam (x:ns) t
                                   goLam ns t =
                                     (". "++) . go letp ns t

    App t u                   -> par p appp $ go appp ns t . (' ':) . go atomp ns u

    Sg "_" a b                -> par p pip $ go appp ns a . (" × "++) . go pip ("_":ns) b

    Sg (freshName ns -> x) a b    -> par p pip $ piBind ns x a . goSg (x:ns) b where
                                   goSg ns (Sg "_" a b) =
                                     (" × "++) . go appp ns a . (" × "++) . go pip ("_":ns) b
                                   goSg ns (Sg (freshName ns -> x) a b) =
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
    Root a                    -> par p pip $ ("√ " ++) . go pip ("L":ns) a
    RootIntro t -> par p letp $ ("rintro " ++) . go letp ("L":ns) t
    RootElim (freshName ns -> x) t -> par p letp $ ("relim "++) . (x++) . (". "++) . go letp (x:ns) t

    Tiny0                     -> ("0"++)
    Tiny1                     -> ("1"++)

    Path (freshName ns -> x) a a0 a1 -> ("PathP ("++) . (x++) . (". "++) . go pip (x:ns) a . (") "++) . go atomp ns a0 . (' ':) . go atomp ns a1
    PLam (freshName ns -> x) t a0 a1 -> par p letp $ ("λ "++) . (x++) . (". "++) . go letp (x:ns) t
    PApp t u a0 a1               -> par p appp $ go appp ns t . (' ':) . go atomp ns u

-- deriving instance Show Tm
instance Show Tm where showsPrec p = prettyTm p []

-- parsing
------------------------------------------------------------

type Parser = Parsec Void String

ws :: Parser ()
ws = L.space C.space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

withPos :: Parser Raw -> Parser Raw
withPos p = RSrcPos <$> getSourcePos <*> p
-- withPos p = p

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
  t <- pRaw
  pure (RRoot t)

pRootIntro = do
  symbol "rintro"
  t <- pRaw
  pure (RRootIntro t)

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
      case withEmptyCtx (initialPos file) (infer t) of
        Left err -> displayError file err
        Right (t, a) -> do
          print $ withEmptyCtx (initialPos file) (nf t)
          putStrLn "  :"
          print $ withEmptyCtx (initialPos file) (quote a)
    ["type"] -> do
      (t, file) <- getRaw
      case withEmptyCtx (initialPos file) (infer t) of
        Left err     -> displayError file err
        Right (t, a) -> print $ withEmptyCtx (initialPos file) (quote a)
    _ -> putStrLn "unknown option"

main :: IO ()
main = mainWith getArgs parseStdin

main' :: String -> String -> IO ()
main' mode src = mainWith (pure [mode]) ((,src) <$> parseString src)

mainFile :: String -> String -> IO ()
mainFile mode fn = mainWith (pure [mode]) (parseFile fn)
