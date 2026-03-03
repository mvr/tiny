module Tiny.Syntax where

import Text.Megaparsec (SourcePos)

newtype Ix = Ix Int deriving (Eq, Show, Num) via Int
newtype Lvl = Lvl Int deriving (Eq, Ord, Show, Num) via Int

type FreshArg = (?fresh :: Lvl)

freshLvl :: (FreshArg => Lvl -> a) -> (FreshArg => a)
freshLvl act =
  let v = ?fresh
   in let ?fresh = ?fresh + 1
       in seq ?fresh (act v)

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
  | RSrcPos SourcePos Raw
  | RVar Name [Raw]
  | RTiny
  | RRoot Raw
  | RRootIntro Raw
  | RRootElim Name Raw
  | RTiny0
  | RTiny1
  | RPath Raw Raw
  deriving (Show)

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
  | Var Ix [Tm]
  | Tiny
  | Root Ty
  | RootIntro Tm
  | RootElim Name Tm
  | Tiny0
  | Tiny1
  | Path Name Ty Tm Tm
  | PLam Name Tm Tm Tm
  | PApp Tm Tm Tm Tm
