module Tiny.Core where

import Tiny.Env
import Tiny.Syntax
import Tiny.Value
import Tiny.Renaming

-- Apply
------------------------------------------------------------

infixl 8 ∙

class Apply a b c | a -> b c where
  (∙) :: (FreshArg, ?globals :: Globals) => a -> b -> c

instance Apply Val Val Val where
  (∙) = doApp

doApp :: (FreshArg, ?globals :: Globals) => Val -> Val -> Val
doApp (VLam _ t) u = t ∙ u
doApp (VTyConFun tc args) u =
  let args' = args ++ [u]
   in if length args' == tyConParamCount tc
        then VTyCon tc args'
        else VTyConFun tc args'
doApp (VConFun ci args) u =
  let args' = args ++ [u]
      arity = conParamCount ci + conFieldCount ci
   in if length args' == arity
        then VCon ci args'
        else VConFun ci args'
doApp (VNeutral ne) a = VNeutral (NApp ne a)
doApp t u = error $ "Unexpected in App: " ++ show t ++ " applied to " ++ show u

instance Apply Closure Val Val where
  (Closure cloenv t) ∙ u =
    let ?env = cloenv {envFresh = max (envFresh cloenv) ?fresh}
     in define u (eval t)

instance Renameable a => Apply (BindTiny a) Lvl a where
  (∙) = doBindTinyApp

-- CoApply
------------------------------------------------------------

class CoApply a b c | a -> b c where
  coapply :: (FreshArg, ?globals :: Globals) => a -> b -> c

instance CoApply Val Lvl Val where
  coapply = doRootElim

doRootElim :: (FreshArg, ?globals :: Globals) => Val -> Lvl -> Val
doRootElim (VRootIntro c) lvl = coapply c lvl
doRootElim (VNeutral ne) lvl = VNeutral (NRootElim (BindTiny "geni" lvl ne)) -- TODO: need to gensym a reasonable name
doRootElim v _ = error $ "Unexpected in relim: " ++ show v

defineUnit :: Lvl -> ((FreshArg, ?globals :: Globals) => EnvArg Val => a) -> ((FreshArg, ?globals :: Globals) => EnvArg Val => a)
defineUnit lvl act =
  let ?env =
        ?env
          { envVars = EnvLock (\v -> sub v lvl (envVars ?env)),
            envLength = 1 + envLength ?env,
            envFresh = 1 + envFresh ?env
          }
      ?fresh = ?fresh + 1
   in act

instance CoApply RootClosure Lvl Val where
  coapply (RootClosure cloenv t) lvl =
    let ?env = cloenv {envFresh = max (envFresh cloenv) ?fresh}
     in defineUnit lvl (eval t)

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

coapplyStuck :: (FreshArg, ?globals :: Globals) => RootClosure -> Val
coapplyStuck (RootClosure cloenv t) =
  let ?env = cloenv {envFresh = max (envFresh cloenv) ?fresh}
   in defineStuck (eval t)

-- Evaluation
------------------------------------------------------------

doFst :: Val -> Val
doFst (VPair a _) = a
doFst (VNeutral ne) = VNeutral (NFst ne)
doFst t = error $ "Unexpected in fst: " ++ show t

doSnd :: Val -> Val
doSnd (VPair _ b) = b
doSnd (VNeutral ne) = VNeutral (NSnd ne)
doSnd t = error $ "Unexpected in snd: " ++ show t

doPApp :: (FreshArg, ?globals :: Globals) => Val -> Val -> Val -> Val -> Val
doPApp _ VTiny0 a0 _ = a0
doPApp _ VTiny1 _ a1 = a1
doPApp (VPLam _ c _ _) t _ _ = c ∙ t
doPApp (VNeutral ne) t a0 a1 = VNeutral (NPApp ne t a0 a1)
doPApp v _ _ _ = error $ "Unexpected in papp: " ++ show v

caseAltVal :: (FreshArg, EnvArg Val, ?globals :: Globals) => CaseAlt -> VCaseAlt
caseAltVal (CaseAlt c xs body) = VCaseAlt c xs (eval (foldr Lam body xs))

findCaseAlt :: Name -> [VCaseAlt] -> Maybe VCaseAlt
findCaseAlt _ [] = Nothing
findCaseAlt c (alt@(VCaseAlt c' _ _) : rest)
  | c == c' = Just alt
  | otherwise = findCaseAlt c rest

doCase :: (FreshArg, ?globals :: Globals) => Val -> Name -> Closure -> [VCaseAlt] -> Val
doCase (VCon ci args) x motive alts =
  let fields = drop (conParamCount ci) args
  in case findCaseAlt (conName ci) alts of
    Just (VCaseAlt _ _ branch) -> foldl doApp branch fields
    Nothing -> error ("missing case alternative for constructor " ++ conName ci)
doCase (VNeutral ne) x motive alts = VNeutral (NCase ne x motive alts)
doCase scrut _ _ _ = error ("Expected constructor in case, got: " ++ show scrut)

eval :: (FreshArg, EnvArg Val, ?globals :: Globals) => Tm -> Val
eval t = case t of
  U -> VU
  Let _ _ t' u -> define (eval t') (eval u)
  Pi x a b -> VPi x (eval a) (Closure ?env b)
  Lam x t' -> VLam x (Closure ?env t')
  Case t' x b alts -> doCase (eval t') x (Closure ?env b) (fmap caseAltVal alts)
  App t' u -> eval t' ∙ eval u
  Sg x a b -> VSg x (eval a) (Closure ?env b)
  Pair a b -> VPair (eval a) (eval b)
  Fst a -> doFst (eval a)
  Snd a -> doSnd (eval a)
  Var x keys -> envLookup (envVars ?env) x (fmap eval keys)
  GlobalVar x -> globalLookup ?globals x
  Tiny -> VTiny
  Root a -> VRoot (RootClosure ?env a)
  RootIntro t' -> VRootIntro (RootClosure ?env t')
  RootElim _ t' -> freshLvl $ \fr -> coapply (define (makeVarLvl fr) (eval t')) fr
  Tiny0 -> VTiny0
  Tiny1 -> VTiny1
  Path x a a0 a1 -> VPath x (Closure ?env a) (eval a0) (eval a1)
  PLam x a a0 a1 -> VPLam x (Closure ?env a) (eval a0) (eval a1)
  PApp p t' a0 a1 -> doPApp (eval p) (eval t') (eval a0) (eval a1)

quote :: (FreshArg, ?globals :: Globals, EnvArg Val) => Val -> Tm
quote = \case
  VU -> U
  VPi x a b -> Pi x (quote a) (defineNextVar \var -> quote (b ∙ var))
  VTyConFun tc args -> foldl App (GlobalVar (tyConName tc)) (fmap quote args)
  VTyCon tc args -> foldl App (GlobalVar (tyConName tc)) (fmap quote args)
  VConFun ci args -> foldl App (GlobalVar (conName ci)) (fmap quote args)
  VCon ci args -> foldl App (GlobalVar (conName ci)) (fmap quote args)
  VSg x a b -> Sg x (quote a) (defineNextVar \var -> quote (b ∙ var))
  VTiny -> Tiny
  VRoot a -> Root (defineStuck (quote (coapplyStuck a)))
  VPath x a a0 a1 -> Path x (defineNextVar \var -> quote (a ∙ var)) (quote a0) (quote a1)
  VLam x c -> Lam x (defineNextVar \var -> quote (c ∙ var))
  VPair fstV sndV -> Pair (quote fstV) (quote sndV)
  VRootIntro c -> RootIntro (defineStuck (quote (coapplyStuck c)))
  VTiny0 -> Tiny0
  VTiny1 -> Tiny1
  VPLam x p a0 a1 -> PLam x (defineNextVar \var -> quote (p ∙ var)) (quote a0) (quote a1)
  VNeutral ne -> quoteNeutral ne

quoteNeutral :: (FreshArg, ?globals :: Globals, EnvArg Val) => Neutral -> Tm
quoteNeutral (NVar x keys) = Var (lvl2Ix ?env x) (fmap quote keys)
quoteNeutral (NGlobalVar x) = GlobalVar x
quoteNeutral (NCase ne x b alts) =
  Case
    (quoteNeutral ne)
    x
    (defineNextVar \var -> quote (b ∙ var))
    (fmap quoteAlt alts)
  where
    quoteAlt (VCaseAlt c xs v) = CaseAlt c xs (quoteCaseBody xs v)
    quoteCaseBody [] v = quote v
    quoteCaseBody (_ : xs) v = defineNextVar \var -> quoteCaseBody xs (v ∙ var)
quoteNeutral (NApp f a) = App (quoteNeutral f) (quote a)
quoteNeutral (NFst a) = Fst (quoteNeutral a)
quoteNeutral (NSnd a) = Snd (quoteNeutral a)
quoteNeutral (NRootElim bt@(BindTiny l _ _)) =
  RootElim l $
    let lvl :: Lvl
        lvl = Lvl (envLength ?env)
     in define (makeVarLvl lvl) $ quoteNeutral (bt ∙ lvl)
quoteNeutral (NPApp p t a0 a1) = PApp (quoteNeutral p) (quote t) (quote a0) (quote a1)

nf :: (FreshArg, ?globals :: Globals) => EnvArg Val => Tm -> Tm
nf t = quote (eval t)

-- Conversion
------------------------------------------------------------

eq :: (FreshArg, ?globals :: Globals) => EnvArg Val => Val -> Val -> Bool
eq VU VU = True
eq (VNeutral ne1) (VNeutral ne2) = eqNE ne1 ne2
eq (VPi _ aty1 bclo1) (VPi _ aty2 bclo2) = eq aty1 aty2 && defineNextVar (\var -> eq (bclo1 ∙ var) (bclo2 ∙ var))
eq (VTyCon tc1 ps1) (VTyCon tc2 ps2) =
  tyConName tc1 == tyConName tc2
    && length ps1 == length ps2
    && and (zipWith eq ps1 ps2)
eq (VTyConFun tc1 ps1) (VTyConFun tc2 ps2) =
  tyConName tc1 == tyConName tc2
    && length ps1 == length ps2
    && and (zipWith eq ps1 ps2)
eq (VCon ci1 sp1) (VCon ci2 sp2) =
  conName ci1 == conName ci2
    && length sp1 == length sp2
    && and (zipWith eq sp1 sp2)
eq (VConFun ci1 sp1) (VConFun ci2 sp2) =
  conName ci1 == conName ci2
    && length sp1 == length sp2
    && and (zipWith eq sp1 sp2)
eq (VSg _ aty1 bclo1) (VSg _ aty2 bclo2) = eq aty1 aty2 && defineNextVar (\var -> eq (bclo1 ∙ var) (bclo2 ∙ var))
eq VTiny VTiny = True
eq (VRoot a) (VRoot a') = defineStuck $ eq (coapplyStuck a) (coapplyStuck a')
eq VTiny0 VTiny0 = True
eq VTiny1 VTiny1 = True
eq (VPath _ c a0 a1) (VPath _ c' a0' a1') =
  defineNextVar (\var -> eq (c ∙ var) (c' ∙ var))
    && eq a0 a0'
    && eq a1 a1'
eq (VLam _ b) (VLam _ b') = defineNextVar (\var -> eq (b ∙ var) (b' ∙ var))
eq (VLam _ b) f' = defineNextVar (\var -> eq (b ∙ var) (f' ∙ var))
eq f (VLam _ b') = defineNextVar (\var -> eq (f ∙ var) (b' ∙ var))
eq (VPair a1 b1) (VPair a2 b2) = eq a1 a2 && eq b1 b2
eq (VPair a1 b1) p2 = eq a1 (doFst p2) && eq b1 (doSnd p2)
eq p1 (VPair a2 b2) = eq (doFst p1) a2 && eq (doSnd p1) b2
eq (VRootIntro a1) (VRootIntro a2) = defineStuck $ eq (coapplyStuck a1) (coapplyStuck a2)
eq (VRootIntro a1) r2 = defineStuck $ eq (coapplyStuck a1) (freshLvl $ \fr -> doRootElim (addKey (makeVarLvl fr) r2) fr)
eq r1 (VRootIntro a2) = defineStuck $ eq (freshLvl $ \fr -> doRootElim (addKey (makeVarLvl fr) r1) fr) (coapplyStuck a2)
eq (VPLam _ a _ _) (VPLam _ a' _ _) = defineNextVar (\var -> eq (a ∙ var) (a' ∙ var))
eq (VPLam _ a _ _) p' = defineNextVar (\var -> eq (a ∙ var) (p' ∙ var))
eq p (VPLam _ a' _ _) = defineNextVar (\var -> eq (p ∙ var) (a' ∙ var))
eq _ _ = False

eqNE :: (FreshArg, ?globals :: Globals) => EnvArg Val => Neutral -> Neutral -> Bool
eqNE (NVar i ikeys) (NVar j jkeys) = i == j && all (uncurry eq) (zip ikeys jkeys)
eqNE (NCase ne1 _ b1 alts1) (NCase ne2 _ b2 alts2) =
  eqNE ne1 ne2
    && defineNextVar (\var -> eq (b1 ∙ var) (b2 ∙ var))
    && length alts1 == length alts2
    && and (zipWith eqAlt alts1 alts2)
  where
    eqAlt (VCaseAlt c1 xs1 v1) (VCaseAlt c2 xs2 v2) =
      c1 == c2 && xs1 == xs2 && eq v1 v2
eqNE (NApp f1 a1) (NApp f2 a2) = eqNE f1 f2 && eq a1 a2
eqNE (NFst p1) (NFst p2) = eqNE p1 p2
eqNE (NSnd p1) (NSnd p2) = eqNE p1 p2
eqNE (NRootElim tb1) (NRootElim tb2) = freshLvl (\fr -> define (makeVarLvl fr) $ eqNE (tb1 ∙ fr) (tb2 ∙ fr))
eqNE (NPApp f1 a1 _ _) (NPApp f2 a2 _ _) = eqNE f1 f2 && eq a1 a2
eqNE _ _ = False

-- Substitution
------------------------------------------------------------

-- Substitutes a value for a variable. This may cause reduction.
class Substitutable a b | a -> b where
  sub :: (FreshArg, ?globals :: Globals) => Val -> Lvl -> a -> b

instance Substitutable Val Val where
  sub v i = \case
    VNeutral n -> sub v i n
    VU -> VU
    VPi x a b -> VPi x (sub v i a) (sub v i b)
    VLam x c -> VLam x (sub v i c)
    VTyConFun tc args -> VTyConFun tc (fmap (sub v i) args)
    VTyCon tc args -> VTyCon tc (fmap (sub v i) args)
    VConFun ci args -> VConFun ci (fmap (sub v i) args)
    VCon ci args -> VCon ci (fmap (sub v i) args)
    VSg x a b -> VSg x (sub v i a) (sub v i b)
    VPair a b -> VPair (sub v i a) (sub v i b)
    VTiny -> VTiny
    VRoot c -> VRoot (sub v i c)
    VRootIntro c -> VRootIntro (sub v i c)
    VTiny0 -> VTiny0
    VTiny1 -> VTiny1
    VPath l c a0 a1 -> VPath l (sub v i c) (sub v i a0) (sub v i a1)
    VPLam l c a0 a1 -> VPLam l (sub v i c) (sub v i a0) (sub v i a1)

-- Not `Substitutable Neutral Val`, because substituting might unstick things
instance Substitutable Neutral Val where
  sub v i = \case
    NVar j ks
      | i == j -> addKeys (fmap (sub v i) ks) v
      | otherwise -> VNeutral (NVar j (fmap (sub v i) ks))
    NGlobalVar x -> VNeutral (NGlobalVar x)
    NCase ne x b alts -> doCase (sub v i ne) x (sub v i b) (fmap (sub v i) alts)
    NApp f a -> sub v i f ∙ sub v i a
    NFst a -> doFst (sub v i a)
    NSnd b -> doSnd (sub v i b)
    NRootElim bt -> freshLvl $ \fr -> doRootElim (sub v i (bt ∙ fr)) fr
    NPApp p t a0 a1 -> doPApp (sub v i p) (sub v i t) (sub v i a0) (sub v i a1)

instance Substitutable Normal Val where
  sub v i (Normal _ a) = sub v i a

instance Substitutable Closure Closure where
  sub v i (Closure env t) = Closure (sub v i env) t

instance Substitutable RootClosure RootClosure where
  sub v i (RootClosure env t) = RootClosure (sub v i env) t

instance Substitutable VCaseAlt VCaseAlt where
  sub v i (VCaseAlt c xs body) = VCaseAlt c xs (sub v i body)

instance Substitutable (BindTiny Neutral) (BindTiny Val) where
  sub v i bt@(BindTiny l _ _) = freshLvl $ \fr -> BindTiny l fr (sub v i (bt ∙ fr))

instance Substitutable (EnvVars Val) (EnvVars Val) where
  sub _ _ EnvEmpty = EnvEmpty
  sub v i (EnvVal e env) = EnvVal (sub v i e) (sub v i env)
  sub v i (EnvLock f) = EnvLock (sub v i . f)

instance Substitutable (Env Val) (Env Val) where
  sub v i env = env {envFresh = max (envFresh env) ?fresh, envVars = sub v i (envVars env)}
