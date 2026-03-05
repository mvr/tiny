module Tiny.Value where

import Tiny.Syntax

data EnvVars v
  = EnvEmpty
  | EnvVal v (EnvVars v)
  | EnvLock (Val -> EnvVars v)

data Env v = Env
  { envVars :: EnvVars v,
    envLength :: Int,
    envFresh :: Lvl
  }
  deriving (Show, Functor)

instance Show v => Show (EnvVars v) where
  showsPrec d EnvEmpty = showString "EnvEmpty"
  showsPrec d (EnvVal v env) =
    showParen (d > 10) $
      showString "EnvVal "
        . showsPrec 11 v
        . showString " "
        . showsPrec 11 env
  showsPrec d (EnvLock _) =
    showParen (d > 10) $ showString "EnvLock <fn>"

instance Functor EnvVars where
  fmap _ EnvEmpty = EnvEmpty
  fmap f (EnvVal v env) = EnvVal (f v) (fmap f env)
  fmap f (EnvLock fenv) = EnvLock (\v -> fmap f (fenv v))

-- TODO: Where should this naturally go
newtype Globals = Globals { globalNames :: [(Name, (Val, VTy))]}

data Closure = Closure (Env Val) Tm

data RootClosure = RootClosure (Env Val) Tm

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
  | VTiny
  | VRoot RootClosure
  | VRootIntro RootClosure
  | VTiny0
  | VTiny1
  | VPath Name Closure Val Val
  | VPLam Name Closure Val Val
  deriving (Show)

data Neutral
  = NApp Neutral Val
  | NFst Neutral
  | NSnd Neutral
  | NVar Lvl [Val]
  | NGlobalVar Name
  | NRootElim (BindTiny Neutral)
  | NPApp Neutral Val Val Val
  deriving (Show)

data Normal = Normal
  { nfTy :: VTy,
    nfTerm :: Val
  }
  deriving (Show)

instance Show Closure where
  showsPrec d (Closure env _) =
    showParen (d > 10) $
      showString "Closure "
        . showsPrec 11 env
        . showString " <tm>"

instance Show RootClosure where
  showsPrec d (RootClosure env _) =
    showParen (d > 10) $
      showString "RootClosure "
        . showsPrec 11 env
        . showString " <tm>"
