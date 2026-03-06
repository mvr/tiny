module Tiny.Env where

import Tiny.Syntax
import Tiny.Value
import Tiny.Renaming

type EnvArg v = (?env :: Env v)

emptyEnv :: Env v
emptyEnv = Env EnvEmpty 0 0

makeVarLvl :: Lvl -> Val
makeVarLvl lvl = VNeutral (NVar lvl [])

makeVar :: Env v -> Val
makeVar env = makeVarLvl (Lvl $ envLength env)

lvl2Ix :: Env v -> Lvl -> Ix
lvl2Ix env (Lvl x) = Ix (envLength env - x - 1)

ix2Lvl :: Env v -> Ix -> Lvl
ix2Lvl env (Ix x) = Lvl (envLength env - x - 1)

-- TODO: use implicit ?env?
envLookup :: EnvVars v -> Ix -> [Val] -> v
envLookup env i keys = go i keys env
  where
    go 0 _ (EnvVal v _) = v
    go j ks (EnvVal _ envtail) = go (j - 1) ks envtail
    go j (k : ks) (EnvLock f) = go (j - 1) ks (f k)
    go _ [] (EnvLock _) = error "Ran out of keys"
    go _ _ EnvEmpty = error "Ran out of environment"

globalLookup :: Globals -> Name -> Val
globalLookup gs x = case lookup x (globalNames gs) of
  Just (v, _) -> v
  Nothing -> error ("No global with name " ++ x)

withFresh :: (FreshArg => Val -> a) -> (FreshArg => a)
withFresh act =
  let v = VNeutral (NVar ?fresh [])
   in let ?fresh = ?fresh + 1
       in seq ?fresh (act v)

define :: v -> (FreshArg => EnvArg v => a) -> (FreshArg => EnvArg v => a)
define v act =
  let ?env =
        ?env
          { envVars = EnvVal v (envVars ?env),
            envLength = 1 + envLength ?env,
            envFresh = 1 + envFresh ?env
          }
      ?fresh = ?fresh + 1
   in act

defineNextVar :: (FreshArg => EnvArg Val => Val -> a) -> (FreshArg => EnvArg Val => a)
defineNextVar act =
  let lvl :: Int
      lvl = envLength ?env
      v = VNeutral (NVar (Lvl lvl) [])
   in define v (act v)
