module Tiny.Pretty where

import Tiny.Syntax

freshName :: [Name] -> Name -> Name
freshName _ "_" = "_"
freshName ns x
  | elem x ns = freshName ns (x ++ "'")
  | otherwise = x

atomp, appp, pip, letp :: Int
atomp = 3
appp = 2
pip = 1
letp = 0

par :: Int -> Int -> ShowS -> ShowS
par p p' = showParen (p' < p)

prettyTm :: Int -> [Name] -> Tm -> ShowS
prettyTm prec = go prec
  where
    piBind ns x a =
      showParen True ((x ++) . (" : " ++) . go letp ns a)

    go :: Int -> [Name] -> Tm -> ShowS
    go p ns = \case
      U -> ("U" ++)
      Let (freshName ns -> x) a t u ->
        par p letp $
          ("let " ++) . (x ++) . (" : " ++) . go letp ns a
            . ("\n    = " ++) . go letp ns t . ("\nin\n" ++) . go letp (x : ns) u
      Pi "_" a b -> par p pip $ go appp ns a . (" → " ++) . go pip ("_" : ns) b
      Pi (freshName ns -> x) a b ->
        par p pip $ piBind ns x a . goPi (x : ns) b
        where
          goPi ns' (Pi "_" a' b') =
            (" → " ++) . go appp ns' a' . (" → " ++) . go pip ("_" : ns') b'
          goPi ns' (Pi (freshName ns' -> x') a' b') =
            piBind ns' x' a' . goPi (x' : ns') b'
          goPi ns' b' =
            (" → " ++) . go pip ns' b'
      Lam (freshName ns -> x) t ->
        par p letp $
          ("λ " ++) . (x ++) . goLam (x : ns) t
        where
          goLam ns' (Lam (freshName ns' -> x') t') =
            (' ' :) . (x' ++) . goLam (x' : ns') t'
          goLam ns' t' =
            (". " ++) . go letp ns' t'
      App t u -> par p appp $ go appp ns t . (' ' :) . go atomp ns u
      Sg "_" a b -> par p pip $ go appp ns a . (" × " ++) . go pip ("_" : ns) b
      Sg (freshName ns -> x) a b ->
        par p pip $ piBind ns x a . goSg (x : ns) b
        where
          goSg ns' (Sg "_" a' b') =
            (" × " ++) . go appp ns' a' . (" × " ++) . go pip ("_" : ns') b'
          goSg ns' (Sg (freshName ns' -> x') a' b') =
            piBind ns' x' a' . goSg (x' : ns') b'
          goSg ns' b' =
            (" × " ++) . go pip ns' b'
      Pair a b -> ("<" ++) . go letp ns a . (", " ++) . go letp ns b . (">" ++)
      Fst a -> par p letp $ ("fst " ++) . go letp ns a
      Snd a -> par p letp $ ("snd " ++) . go letp ns a
      Var (Ix x) [] -> (ns !! x ++)
      Var (Ix x) keys ->
        (ns !! x ++) . ('[' :) . goKeys keys . (']' :)
        where
          goKeys [] = id
          goKeys [k] = go p ns k
          goKeys (k : ks) = go p ns k . (", " ++) . goKeys ks
      GlobalVar x -> (x ++)
      Tiny -> ("T" ++)
      Root a -> par p pip $ ("√ " ++) . go pip ("L" : ns) a
      RootIntro t -> par p letp $ ("rintro " ++) . go letp ("L" : ns) t
      RootElim (freshName ns -> x) t ->
        par p letp $ ("relim " ++) . (x ++) . (". " ++) . go letp (x : ns) t
      Tiny0 -> ("t0" ++)
      Tiny1 -> ("t1" ++)
      Path (freshName ns -> x) a a0 a1 ->
        ("PathP (" ++) . (x ++) . (". " ++) . go pip (x : ns) a . (") " ++) . go atomp ns a0 . (' ' :) . go atomp ns a1
      PLam (freshName ns -> x) t _ _ ->
        par p letp $ ("λ " ++) . (x ++) . (". " ++) . go letp (x : ns) t
      PApp t u _ _ ->
        par p appp $ go appp ns t . (' ' :) . go atomp ns u

instance Show Tm where
  showsPrec p = prettyTm p []
