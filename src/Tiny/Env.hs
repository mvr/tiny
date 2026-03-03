module Tiny.Env where

import Tiny.Syntax
import Tiny.Value

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

envLookup :: EnvVars v -> Ix -> [Val] -> v
envLookup env i keys = go i keys env
  where
    go 0 _ (EnvVal v _) = v
    go j ks (EnvVal _ envtail) = go (j - 1) ks envtail
    go j (k : ks) (EnvLock f) = go (j - 1) ks (f k)
    go _ [] (EnvLock _) = error "Ran out of keys"
    go _ _ EnvEmpty = error "Ran out of environment"
