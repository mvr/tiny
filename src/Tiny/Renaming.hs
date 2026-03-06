module Tiny.Renaming where

import Tiny.Syntax
import Tiny.Value

-- Renaming
------------------------------------------------------------

-- Switch one de Bruijn level for another.
class Renameable a where
  rename :: FreshArg => Lvl -> Lvl -> a -> a

doBindTinyApp :: (FreshArg, Renameable a) => BindTiny a -> Lvl -> a
doBindTinyApp (BindTiny _ i a) j
    | i == j = a
    | otherwise = rename j i a

instance Renameable Val where
  rename v i = \case
    VNeutral n -> VNeutral (rename v i n)
    VU -> VU
    VPi x a b -> VPi x (rename v i a) (rename v i b)
    VLam x c -> VLam x (rename v i c)
    VTyConFun tc ps -> VTyConFun tc (fmap (rename v i) ps)
    VTyCon tc ps -> VTyCon tc (fmap (rename v i) ps)
    VConFun ci sp -> VConFun ci (fmap (rename v i) sp)
    VCon ci sp -> VCon ci (fmap (rename v i) sp)
    VSqc sqc -> VSqc sqc
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
    NGlobalVar x -> NGlobalVar x
    NCase ne x b alts -> NCase (rename v i ne) x (rename v i b) (fmap (rename v i) alts)
    NApp f a -> NApp (rename v i f) (rename v i a)
    NFst a -> NFst (rename v i a)
    NSnd a -> NSnd (rename v i a)
    NSqc sqc f -> NSqc sqc (rename v i f)
    NRootElim bt -> NRootElim (rename v i bt)
    NPApp p i' a0 a1 -> NPApp (rename v i p) (rename v i i') (rename v i a0) (rename v i a1)

instance Renameable Normal where
  rename v i (Normal ty a) = Normal (rename v i ty) (rename v i a)

instance Renameable Closure where
  rename v i (Closure env t) = Closure (rename v i env) t

instance Renameable RootClosure where
  rename v i (RootClosure env t) = RootClosure (rename v i env) t

instance Renameable VCaseAlt where
  rename v i (VCaseAlt c xs body) = VCaseAlt c xs (rename v i body)

instance Renameable a => Renameable (BindTiny a) where
  rename v i bt@(BindTiny l j _)
    | v == j = freshLvl $ \fr -> BindTiny l fr (rename v i (doBindTinyApp bt fr))
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

-- Keying
------------------------------------------------------------

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
    VTyConFun tc ps -> VTyConFun tc (fmap (addKeys ks) ps)
    VTyCon tc ps -> VTyCon tc (fmap (addKeys ks) ps)
    VConFun ci sp -> VConFun ci (fmap (addKeys ks) sp)
    VCon ci sp -> VCon ci (fmap (addKeys ks) sp)
    VSqc sqc -> VSqc sqc
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
    NGlobalVar x -> NGlobalVar x
    NCase ne x b alts -> NCase (addKeys ks ne) x (addKeys ks b) (fmap (addKeys ks) alts)
    NApp f a -> NApp (addKeys ks f) (addKeys ks a)
    NFst a -> NFst (addKeys ks a)
    NSnd a -> NSnd (addKeys ks a)
    NSqc sqc f -> NSqc sqc (addKeys ks f)
    NRootElim bt -> NRootElim (addKeys ks bt)
    NPApp p i a0 a1 -> NPApp (addKeys ks p) (addKeys ks i) (addKeys ks a0) (addKeys ks a1)

instance Keyable Normal where
  addKeys ks (Normal ty a) = Normal (addKeys ks ty) (addKeys ks a)

instance Keyable Closure where
  addKeys ks (Closure env t) = Closure (addKeys ks env) t

instance Keyable RootClosure where
  addKeys ks (RootClosure env t) = RootClosure (addKeys ks env) t

instance Keyable VCaseAlt where
  addKeys ks (VCaseAlt c xs body) = VCaseAlt c xs (addKeys ks body)

instance (Keyable a, Renameable a) => Keyable (BindTiny a) where
  addKeys ks bt@(BindTiny l _ _) = freshLvl $ \fr -> BindTiny l fr (addKeys ks (doBindTinyApp bt fr))

instance Keyable v => Keyable (EnvVars v) where
  addKeys _ EnvEmpty = EnvEmpty
  addKeys ks (EnvVal v env) = EnvVal (addKeys ks v) (addKeys ks env)
  addKeys ks (EnvLock f) = EnvLock (addKeys ks . f)

instance Keyable v => Keyable (Env v) where
  addKeys ks env = env {envFresh = max (envFresh env) ?fresh, envVars = addKeys ks (envVars env)}
