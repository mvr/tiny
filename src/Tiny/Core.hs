module Tiny.Core where

import Tiny.Env
import Tiny.Syntax
import Tiny.Value

infixl 8 ∙

class Apply a b c | a -> b c where
  (∙) :: FreshArg => a -> b -> c

class CoApply a b c | a -> b c where
  coapply :: FreshArg => a -> b -> c

-- Appends keys to all free variables. This cannot cause reduction.
class Keyable a where
  addKeys :: FreshArg => [Val] -> a -> a
  addKey :: FreshArg => Val -> a -> a
  addKey k = addKeys [k]

instance Keyable Name where
  addKeys _ n = n

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
  addKeys ks bt@(BindTiny l _ _) = freshLvl $ \fr -> BindTiny l fr (addKeys ks (bt ∙ fr))

instance Keyable v => Keyable (EnvVars v) where
  addKeys _ EnvEmpty = EnvEmpty
  addKeys ks (EnvVal v env) = EnvVal (addKeys ks v) (addKeys ks env)
  addKeys ks (EnvLock f) = EnvLock (addKeys ks . f)

instance Keyable v => Keyable (Env v) where
  addKeys ks env = env {envFresh = max (envFresh env) ?fresh, envVars = addKeys ks (envVars env)}

-- Substitutes a value for a variable. This may cause reduction.
class Substitutable a b | a -> b where
  sub :: FreshArg => Val -> Lvl -> a -> b

instance (Apply Closure Val Val, CoApply RootClosure Lvl Val) => Substitutable Val Val where
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

instance (Apply Closure Val Val, CoApply RootClosure Lvl Val) => Substitutable Neutral Val where
  sub v i = \case
    NVar j ks
      | i == j -> addKeys (fmap (sub v i) ks) v
      | otherwise -> VNeutral (NVar j (fmap (sub v i) ks))
    NApp f a -> sub v i f ∙ sub v i a
    NFst a -> doFst (sub v i a)
    NSnd b -> doSnd (sub v i b)
    NRootElim bt -> freshLvl $ \fr -> doRootElim (sub v i (bt ∙ fr)) fr
    NPApp p t a0 a1 -> doPApp (sub v i p) (sub v i t) (sub v i a0) (sub v i a1)

instance (Apply Closure Val Val, CoApply RootClosure Lvl Val) => Substitutable Normal Val where
  sub v i (Normal _ a) = sub v i a

instance (Apply Closure Val Val, CoApply RootClosure Lvl Val) => Substitutable Closure Closure where
  sub v i (Closure env t) = Closure (sub v i env) t

instance (Apply Closure Val Val, CoApply RootClosure Lvl Val) => Substitutable RootClosure RootClosure where
  sub v i (RootClosure env t) = RootClosure (sub v i env) t

instance (Apply Closure Val Val, CoApply RootClosure Lvl Val) => Substitutable (BindTiny Neutral) (BindTiny Val) where
  sub v i bt@(BindTiny l _ _) = freshLvl $ \fr -> BindTiny l fr (sub v i (bt ∙ fr))

instance (Apply Closure Val Val, CoApply RootClosure Lvl Val) => Substitutable (EnvVars Val) (EnvVars Val) where
  sub _ _ EnvEmpty = EnvEmpty
  sub v i (EnvVal e env) = EnvVal (sub v i e) (sub v i env)
  sub v i (EnvLock f) = EnvLock (sub v i . f)

instance (Apply Closure Val Val, CoApply RootClosure Lvl Val) => Substitutable (Env Val) (Env Val) where
  sub v i env = env {envFresh = max (envFresh env) ?fresh, envVars = sub v i (envVars env)}

-- Switch one de Bruijn level for another.
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
    NVar j ks
      | i == j -> NVar v (fmap (rename v i) ks)
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
  rename v i bt@(BindTiny l j _)
    | v == j = freshLvl $ \fr -> BindTiny l fr (rename v i (bt ∙ fr))
    | otherwise = BindTiny l j (rename v i a)
    where
      BindTiny _ _ a = bt

instance Renameable v => Renameable (EnvVars v) where
  rename _ _ EnvEmpty = EnvEmpty
  rename v i (EnvVal e env) = EnvVal (rename v i e) (rename v i env)
  rename v i (EnvLock f) = EnvLock (rename v i . f)

instance Renameable (Env Val) where
  rename v i env =
    env
      { envFresh = max (envFresh env) ?fresh,
        envVars = rename v i (envVars env)
      }

doApp :: (FreshArg, Apply Closure Val Val) => Val -> Val -> Val
doApp (VLam _ t) u = t ∙ u
doApp (VNeutral ne) a = VNeutral (NApp ne a)
doApp t u = error $ "Unexpected in App: " ++ show t ++ " applied to " ++ show u

doFst :: Val -> Val
doFst (VPair a _) = a
doFst (VNeutral ne) = VNeutral (NFst ne)
doFst t = error $ "Unexpected in fst: " ++ show t

doSnd :: Val -> Val
doSnd (VPair _ b) = b
doSnd (VNeutral ne) = VNeutral (NSnd ne)
doSnd t = error $ "Unexpected in snd: " ++ show t

doRootElim :: (FreshArg, CoApply RootClosure Lvl Val) => Val -> Lvl -> Val
doRootElim (VRootIntro c) lvl = coapply c lvl
doRootElim (VNeutral ne) lvl = VNeutral (NRootElim (BindTiny "geni" lvl ne))
doRootElim v _ = error $ "Unexpected in relim: " ++ show v

doPApp :: (FreshArg, Apply Closure Val Val) => Val -> Val -> Val -> Val -> Val
doPApp _ VTiny0 a0 _ = a0
doPApp _ VTiny1 _ a1 = a1
doPApp (VPLam _ c _ _) t _ _ = c ∙ t
doPApp (VNeutral ne) t a0 a1 = VNeutral (NPApp ne t a0 a1)
doPApp v _ _ _ = error $ "Unexpected in papp: " ++ show v

fresh :: (FreshArg => Val -> a) -> (FreshArg => a)
fresh act =
  let v = VNeutral (NVar ?fresh [])
   in let ?fresh = ?fresh + 1
       in seq ?fresh (act v)

defineUnit :: Lvl -> (FreshArg => EnvArg Val => a) -> (FreshArg => EnvArg Val => a)
defineUnit lvl act =
  let ?env =
        ?env
          { envVars = EnvLock (\v -> sub v lvl (envVars ?env)),
            envLength = 1 + envLength ?env,
            envFresh = 1 + envFresh ?env
          }
      ?fresh = ?fresh + 1
   in act

defineStuck :: Keyable v => (FreshArg => EnvArg v => a) -> (FreshArg => EnvArg v => a)
defineStuck act =
  let ?env =
        ?env
          { envVars = EnvLock (\v -> addKey v (envVars ?env)),
            envLength = 1 + envLength ?env,
            envFresh = 1 + envFresh ?env
          }
      ?fresh = ?fresh + 1
   in act

nextVar :: (FreshArg => EnvArg Val => Val -> a) -> (FreshArg => EnvArg Val => a)
nextVar act =
  let lvl :: Int
      lvl = envLength ?env
      v = VNeutral (NVar (Lvl lvl) [])
   in define v (act v)

instance Renameable a => Apply (BindTiny a) Lvl a where
  (BindTiny _ i a) ∙ j
    | i == j = a
    | otherwise = rename j i a

instance Apply Closure Val Val => Apply Val Val Val where
  (∙) = doApp

instance CoApply RootClosure Lvl Val => CoApply Val Lvl Val where
  coapply = doRootElim

instance Apply Closure Val Val where
  (Closure cloenv t) ∙ u =
    let ?env = cloenv {envFresh = max (envFresh cloenv) ?fresh}
     in define u (eval t)

instance CoApply RootClosure Lvl Val where
  coapply (RootClosure cloenv t) lvl =
    let ?env = cloenv {envFresh = max (envFresh cloenv) ?fresh}
     in defineUnit lvl (eval t)

appRootClosureStuck :: FreshArg => RootClosure -> Val
appRootClosureStuck (RootClosure cloenv t) =
  let ?env = cloenv {envFresh = max (envFresh cloenv) ?fresh}
   in defineStuck (eval t)

doRootElimEta :: FreshArg => EnvArg v => Val -> Val
doRootElimEta r = freshLvl $ \fr -> doRootElim (addKey (makeVarLvl fr) r) fr

eval :: FreshArg => EnvArg Val => Tm -> Val
eval t = case t of
  U -> VU
  Let _ _ t' u -> define (eval t') (eval u)
  Pi x a b -> VPi x (eval a) (Closure ?env b)
  Lam x t' -> VLam x (Closure ?env t')
  App t' u -> eval t' ∙ eval u
  Sg x a b -> VSg x (eval a) (Closure ?env b)
  Pair a b -> VPair (eval a) (eval b)
  Fst a -> doFst (eval a)
  Snd a -> doSnd (eval a)
  Var x keys -> envLookup (envVars ?env) x (fmap eval keys)
  Tiny -> VTiny
  Root a -> VRoot (RootClosure ?env a)
  RootIntro t' -> VRootIntro (RootClosure ?env t')
  RootElim _ t' -> freshLvl $ \fr -> coapply (define (makeVarLvl fr) (eval t')) fr
  Tiny0 -> VTiny0
  Tiny1 -> VTiny1
  Path x a a0 a1 -> VPath x (Closure ?env a) (eval a0) (eval a1)
  PLam x a a0 a1 -> VPLam x (Closure ?env a) (eval a0) (eval a1)
  PApp p t' a0 a1 -> doPApp (eval p) (eval t') (eval a0) (eval a1)

quote :: FreshArg => EnvArg Val => Val -> Tm
quote = \case
  VU -> U
  VPi x a b -> Pi x (quote a) (nextVar \var -> quote (b ∙ var))
  VSg x a b -> Sg x (quote a) (nextVar \var -> quote (b ∙ var))
  VTiny -> Tiny
  VRoot a -> Root (defineStuck (quote (appRootClosureStuck a)))
  VPath x a a0 a1 -> Path x (nextVar \var -> quote (a ∙ var)) (quote a0) (quote a1)
  VLam x c -> Lam x (nextVar \var -> quote (c ∙ var))
  VPair fstV sndV -> Pair (quote fstV) (quote sndV)
  VRootIntro c -> RootIntro (defineStuck (quote (appRootClosureStuck c)))
  VTiny0 -> Tiny0
  VTiny1 -> Tiny1
  VPLam x p a0 a1 -> PLam x (nextVar \var -> quote (p ∙ var)) (quote a0) (quote a1)
  VNeutral ne -> quoteNeutral ne
  v -> error $ "Can't quote " ++ show v

quoteNeutral :: FreshArg => EnvArg Val => Neutral -> Tm
quoteNeutral (NVar x keys) = Var (lvl2Ix ?env x) (fmap quote keys)
quoteNeutral (NApp f a) = App (quoteNeutral f) (quote a)
quoteNeutral (NFst a) = Fst (quoteNeutral a)
quoteNeutral (NSnd a) = Snd (quoteNeutral a)
quoteNeutral (NRootElim bt@(BindTiny l _ _)) =
  RootElim l $
    let lvl :: Lvl
        lvl = Lvl (envLength ?env)
     in define (makeVarLvl lvl) $ quoteNeutral (bt ∙ lvl)
quoteNeutral (NPApp p t a0 a1) = PApp (quoteNeutral p) (quote t) (quote a0) (quote a1)

nf :: FreshArg => EnvArg Val => Tm -> Tm
nf t = quote (eval t)

eq :: FreshArg => EnvArg Val => Val -> Val -> Bool
eq VU VU = True
eq (VNeutral ne1) (VNeutral ne2) = eqNE ne1 ne2
eq (VPi _ aty1 bclo1) (VPi _ aty2 bclo2) = eq aty1 aty2 && nextVar (\var -> eq (bclo1 ∙ var) (bclo2 ∙ var))
eq (VSg _ aty1 bclo1) (VSg _ aty2 bclo2) = eq aty1 aty2 && nextVar (\var -> eq (bclo1 ∙ var) (bclo2 ∙ var))
eq VTiny VTiny = True
eq (VRoot a) (VRoot a') = defineStuck $ eq (appRootClosureStuck a) (appRootClosureStuck a')
eq (VPath _ c a0 a1) (VPath _ c' a0' a1') =
  nextVar (\var -> eq (c ∙ var) (c' ∙ var))
    && eq a0 a0'
    && eq a1 a1'
eq (VLam _ b) (VLam _ b') = nextVar (\var -> eq (b ∙ var) (b' ∙ var))
eq (VLam _ b) f' = nextVar (\var -> eq (b ∙ var) (f' ∙ var))
eq f (VLam _ b') = nextVar (\var -> eq (f ∙ var) (b' ∙ var))
eq (VPair a1 b1) (VPair a2 b2) = eq a1 a2 && eq b1 b2
eq (VPair a1 b1) p2 = eq a1 (doFst p2) && eq b1 (doSnd p2)
eq p1 (VPair a2 b2) = eq (doFst p1) a2 && eq (doSnd p1) b2
eq (VRootIntro a1) (VRootIntro a2) = defineStuck $ eq (appRootClosureStuck a1) (appRootClosureStuck a2)
eq (VRootIntro a1) r2 = defineStuck $ eq (appRootClosureStuck a1) (doRootElimEta r2)
eq r1 (VRootIntro a2) = defineStuck $ eq (doRootElimEta r1) (appRootClosureStuck a2)
eq (VPLam _ a _ _) (VPLam _ a' _ _) = nextVar (\var -> eq (a ∙ var) (a' ∙ var))
eq (VPLam _ a _ _) p' = nextVar (\var -> eq (a ∙ var) (p' ∙ var))
eq p (VPLam _ a' _ _) = nextVar (\var -> eq (p ∙ var) (a' ∙ var))
eq _ _ = False

eqNE :: FreshArg => EnvArg Val => Neutral -> Neutral -> Bool
eqNE (NVar i ikeys) (NVar j jkeys) = i == j && all (uncurry eq) (zip ikeys jkeys)
eqNE (NApp f1 a1) (NApp f2 a2) = eqNE f1 f2 && eq a1 a2
eqNE (NFst p1) (NFst p2) = eqNE p1 p2
eqNE (NSnd p1) (NSnd p2) = eqNE p1 p2
eqNE (NRootElim tb1) (NRootElim tb2) = freshLvl (\fr -> define (makeVarLvl fr) $ eqNE (tb1 ∙ fr) (tb2 ∙ fr))
eqNE (NPApp f1 a1 _ _) (NPApp f2 a2 _ _) = eqNE f1 f2 && eq a1 a2
eqNE _ _ = False
