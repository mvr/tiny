-- TODO:
-- OK, I need a new plan. Say we are evaluating a term
-- key^t_L (λ x. a)

-- Then there are a couple of possibilities: if there has already been
-- a beta redex for the lock L, then this will need to put the term t
-- in the place of whatever variable y was in the redex.

-- Otherwise, the key should end up at the leaves of a

-- So VRootIntro needs to accept a closure (that binds no new variables)

module Main where

import Debug.Trace

import Control.Applicative hiding (many, some)
import Control.Monad
import Data.Char
import Data.Void
import System.Environment
import System.Exit
import Text.Megaparsec
import qualified Text.Megaparsec.Char as C
import qualified Text.Megaparsec.Char.Lexer as L
import Text.Printf
import Prelude hiding (lookup)

-- examples
--------------------------------------------------------------------------------

ex0 = main' "nf" $ unlines [
  "let id : (A : U) -> A -> A",
  "     = \\A x. x in",
  "let foo : U = U in",
  "let bar : U = id id in",     -- we cannot apply any function to itself (already true in simple TT)
  "id"
  ]

rex0 =
  main' "nf" $
    unlines
      [ "let counit : (root L T) -> T",
        "     = \\x. relim i. x in",
        "counit"
      ]

-- -- basic polymorphic functions
-- ex1 = main' "nf" $ unlines [
--   "let id : (A : U) -> A -> A",
--   "      = \\A x. x in",
--   "let const : (A B : U) -> A -> B -> A",
--   "      = \\A B x y. x in",
--   "id ((A B : U) -> A -> B -> A) const"
--   ]

-- -- Church-coded natural numbers (standard test for finding eval bugs)
-- ex2 = main' "nf" $ unlines [
--   "let Nat  : U = (N : U) -> (N -> N) -> N -> N in",
--   "let five : Nat = \\N s z. s (s (s (s (s z)))) in",
--   "let add  : Nat -> Nat -> Nat = \\a b N s z. a N s (b N s z) in",
--   "let mul  : Nat -> Nat -> Nat = \\a b N s z. a N (b N s) z in",
--   "let ten      : Nat = add five five in",
--   "let hundred  : Nat = mul ten ten in",
--   "let thousand : Nat = mul ten hundred in",
--   "thousand"
--   ]

-- syntax
--------------------------------------------------------------------------------

-- Minimal bidirectional elaboration
--   surface syntax vs core syntax
--      (intermediate: raw syntax -->(scope checking) -->raw syntax with indices
--   (our case: difference: no de Bruijn indices in surface syntax, but they're in core syntax)

-- | De Bruijn index.
newtype Ix = Ix Int deriving (Eq, Show, Num) via Int

-- | De Bruijn level.
newtype Lvl = Lvl Int deriving (Eq, Show, Num) via Int

newtype LockIx = LockIx Int deriving (Eq, Show, Num) via Int

newtype LockLvl = LockLvl Int deriving (Eq, Show, Num) via Int

type Name = String

type LockName = String

data Raw
  = RVar Name -- x
  | RLam Name Raw -- \x. t                            -- let f : A -> B = \x -> ....
  | RApp Raw Raw -- t u
  | RU -- U
  | RPi Name Raw Raw -- (x : A) -> B
  | RLet Name Raw Raw Raw -- let x : A = t in u
  | RSrcPos SourcePos Raw -- source position for error reporting
  | RTiny
  | RKey LockName Raw Raw
  | RRoot LockName Raw
  | RRootIntro LockName Raw
  | RRootElim Name Raw
  deriving (Show)

-- core syntax
------------------------------------------------------------

type Ty = Tm

data Tm
  = Var Ix
  | Lam Name Tm
  | App Tm Tm
  | U
  | Pi Name Ty Ty
  | Let Name Ty Tm Tm
  -- New:
  | Tiny
  | Key Tm Tm
  | RootIntro Tm
  | RootElim Name Tm
  | Root LockName Ty

-- values
------------------------------------------------------------

data Entry
  = EnvVal Val
  | EnvRef LockLvl
  | EnvLock
  deriving (Show)
data Env = Env [Entry] [Val]
  deriving (Show)

extVal :: Env -> Val -> Env
extVal (Env vs keys) v = Env (EnvVal v : vs) keys

extLock :: Env -> () -> Env
extLock (Env vs keys) v = Env (EnvLock : vs) keys

extKey :: Env -> Val -> Env
extKey (Env vs keys) v = Env vs (v : keys)

makeVar :: Env -> VTy -> Val
makeVar (Env vs _) a = VNeutral a (NVar (Lvl (length vs)))

data Closure = Closure Env Tm
  deriving (Show)
data LockClosure = LockClosure Env Tm
  deriving (Show)
type VTy = Val

data Val
  = VNeutral ~VTy Neutral
  | VLam Name Closure
  | VPi Name ~VTy Closure
  | VU
  -- New:
  | VTiny
  | VDelayedKey ~Val ~Val
  | VRoot LockName LockClosure
  | VRootIntro LockClosure
  deriving (Show)

data Neutral
  = NVar Lvl
  | NApp Neutral ~Normal
  -- New:
  | NRootElim Name VTy Closure
  deriving (Show)
data Normal = Normal {nfTy :: VTy, nfTerm :: Val}
  deriving (Show)
--------------------------------------------------------------------------------

infixl 8 $$

lvl2Ix :: Env -> Lvl -> Ix
lvl2Ix (Env vs keys) (Lvl x) = Ix (length vs - x - 1)

ix2Lvl :: [a] -> Ix -> Lvl
ix2Lvl as (Ix x) = Lvl (length as - x - 1)

(!!<) :: [a] -> Int -> a
as !!< i = as !! (length as - i - 1)

($$) :: Closure -> Val -> Valv
($$) (Closure (Env vs keys) t) ~u = eval (Env (EnvVal u : vs) keys) t

-- ($$^) :: Closure -> LockLvl -> Val
-- ($$^) (Closure (Env vs keys) t) l = eval (Env (EnvRef l : vs) keys) t

runLock :: LockClosure -> Val
runLock (LockClosure (Env vs keys) t) = eval (Env (EnvLock : vs) keys) t

applyUnit :: LockClosure -> Val
applyUnit (LockClosure (Env (_ : vs) keys) t) = eval (Env (EnvLock : EnvRef (LockLvl (length keys)) : vs) keys) t
applyUnit (LockClosure (Env [] keys) t) = error "impossible applyUnit"

delayVar :: Env -> Ix -> Val -> Val
delayVar env 0 t = t
delayVar env@(Env (EnvVal _ : vs) keys) i t = delayVar (Env vs keys) (i - 1) t
delayVar env@(Env (EnvRef _ : vs) keys) i t = delayVar (Env vs keys) (i - 1) t
delayVar env@(Env (EnvLock : vs) (u : keys)) i t = VDelayedKey u (delayVar (Env vs keys) (i - 1) t)
delayVar env _ t = error "impossible delayVar"

delayKey :: Env -> LockLvl -> Val -> Val
delayKey env@(Env vs keys) i t | i == LockLvl (length keys) = t
delayKey env@(Env (EnvVal _ : vs) keys) i t = delayKey (Env vs keys) i t
delayKey env@(Env (EnvRef _ : vs) keys) i t = delayKey (Env vs keys) i t
delayKey env@(Env (EnvLock : vs) (u : keys)) i t = VDelayedKey u (delayKey (Env vs keys) i t)
delayKey env _ t = error "impossible delayKey"

keyEntry :: Val -> Entry -> Entry
keyEntry u (EnvVal t) = EnvVal (VDelayedKey u t)
keyEntry u (EnvRef l) = EnvRef l
keyEntry u (EnvLock) = EnvLock

keyClosure :: Val -> Closure -> Closure
keyClosure u (Closure (Env vs keys) t) = Closure (Env (fmap (keyEntry u) vs) (fmap (VDelayedKey u) keys)) t

forceKeys :: Val -> Val
forceKeys (VDelayedKey u t) = case forceKeys t of
  VLam x c -> VLam x (keyClosure u c)
  t -> VDelayedKey u t
forceKeys t = t

doApp :: Val -> Val -> Val
doApp (VLam _ t) u = t $$ u
doApp (VNeutral (VPi x aty bclo) ne) a =
  let bty = bclo $$ a
   in VNeutral bty (NApp ne (Normal aty a))
doApp t u = error "Unexpected in App"

doRootElim :: Name -> Env -> Tm -> Val -> Val
doRootElim x env t (VRootIntro c) = applyUnit c
-- The following can't be right, what if c was closed before the new variable existed?
doRootElim x env t (VNeutral (VRoot l c) _) = VNeutral (applyUnit c) (NRootElim x (VRoot l a) (Closure env t))
doRootElim x env t v = error "Unexpected in RootElim"

eval :: Env -> Tm -> Val
eval env@(Env vs keys) = \case
  Var (Ix x) -> case vs !! x of
    EnvVal v -> delayVar env (Ix x) v
    EnvRef (LockLvl lockl) -> delayKey env (LockLvl lockl) (keys !!< lockl)
    EnvLock -> error "impossible eval var"
  Lam x t -> VLam x (Closure env t)
  App t u -> doApp (forceKeys $ eval env t) (eval env u)
  Pi x a b -> VPi x (eval env a) (Closure env b)
  Let x _ t u -> eval (env `extVal` eval env t) u
  U -> VU
  Tiny -> VTiny
  Key t u -> eval (env `extKey` eval env t) u
  Root l a -> VRoot l (LockClosure env a)
  RootIntro t -> VRootIntro (LockClosure env t)
  RootElim x t -> doRootElim x env t (forceKeys $ eval (env `extVal` var) t)
    where
      var = makeVar env VTiny

quoteType :: Env -> VTy -> Tm
quoteType env VU = U
quoteType env (VPi x a b) = Pi x (quoteType env a) (quoteType (env `extVal` var) (b $$ var))
  where
    var = makeVar env a
quoteType env VTiny = Tiny
quoteType env (VRoot x c) = Root x (quoteType (env `extLock` ()) (runLock c))
quoteType env t = error "type expected"

quote :: Env -> VTy -> Val -> Tm
quote env VU vty = quoteType env vty
quote env (VNeutral _ _) (VNeutral _ ne) = quoteNeutral env ne
quote env (VPi x a b) (VLam x' c) = Lam x (quote (env `extVal` var) (b $$ var) (c $$ var))
  where
    var = makeVar env a
quote env (VPi x a b) f = Lam x (quote (env `extVal` var) (b $$ var) (doApp f var))
  where
    var = makeVar env a

-- quote env ty (VDelayedKey u t) = quote (EnvKey u : env) t
-- quote env (VRoot l a) (VRootIntro c) = RootIntro (quote (EnvVar : env) (runLock c))
quote env (VRoot l a) r =
  RootIntro
    ( quote
        (env `extLock` ())
        (runLock a)
        (doRootElim l (env `extLock` ()) recur (VDelayedKey var r))
    )
  where
    var = makeVar (env `extLock` ()) VTiny
    ~recur = Key (Var 0) (quote (env `extLock` () `extVal` var) (VRoot l a) r)

restoreKeys :: Env -> Env -> Ix -> Tm -> Tm
restoreKeys orig (Env _ keys) (Ix 0) u = foldl (\u k -> Key (quote orig VTiny k) u) u keys
restoreKeys orig (Env (EnvVal _ : vs) keys) (Ix i) u = restoreKeys orig (Env vs keys) (Ix (i - 1)) u
restoreKeys orig (Env (EnvRef _ : vs) keys) (Ix i) u = restoreKeys orig (Env vs keys) (Ix (i - 1)) u
restoreKeys orig (Env (EnvLock : vs) (k:keys)) (Ix i) u = restoreKeys orig (Env vs keys) (Ix (i - 1)) u
restoreKeys orig (Env [] _) (Ix i) v = error "impossible restoreKeys"

quoteNeutral :: Env -> Neutral -> Tm
quoteNeutral env = \case
  NVar x -> restoreKeys env env (lvl2Ix env x) (Var (lvl2Ix env x))
  NApp f (Normal aty a) -> App (quoteNeutral env f) (quote env aty a)
  NRootElim x a c -> case c $$ var of
    VNeutral r t -> RootElim x (quoteNeutral (env `extVal` var) t)
    _ -> error "Closure didn't contain a neutral"
    where
      var = makeVar env VTiny

nf :: Env -> VTy -> Tm -> Tm
nf env@(Env vs keys) a t = quote env a (eval env t)

eqTy :: Env -> VTy -> VTy -> Bool
eqTy env VU VU = True
eqTy env (VNeutral _ ne1) (VNeutral _ ne2) = eqNE env ne1 ne2
eqTy env (VPi _ aty1 bclo1) (VPi _ aty2 bclo2) =
  let var = makeVar env aty1
   in eqTy env aty1 aty2
        && eqTy (env `extVal` var) (bclo1 $$ var) (bclo2 $$ var)

eqTy env VTiny VTiny = True
eqTy env (VRoot _ a) (VRoot _ a') = eqTy (env `extLock` ()) (runLock a) (runLock a')
eqTy _ _ _ = False

eqNF :: Env -> (VTy, Val) -> (VTy, Val) -> Bool
--eqNF size p1 p2 | traceShow ("eqNF:", p1, p2) False = undefined
eqNF env (VU, ty1) (VU, ty2) = eqTy env ty1 ty2
eqNF env (VNeutral _ _, VNeutral _ ne1) (VNeutral _ _, VNeutral _ ne2) = eqNE env ne1 ne2
eqNF env (VPi _ aty1 bclo1, f1) (VPi _ aty2 bclo2, f2) =
  let var = makeVar env aty1
   in eqNF (env `extVal` var) (bclo1 $$ var, doApp f1 var) (bclo2 $$ var, doApp f2 var)

eqNF env (VRoot l1 aty1, r1) (VRoot l2 aty2, r2) =
  let var = makeVar (env `extLock` ()) VTiny
      recur1 = Key (Var 0) (quote (env `extLock` () `extVal` var) (VRoot l1 aty1) r1)
      recur2 = Key (Var 0) (quote (env `extLock` () `extVal` var) (VRoot l2 aty2) r2)
  in eqNF (env `extLock` ())
     (runLock aty1, doRootElim l1 (env `extLock` ()) recur1 (VDelayedKey var r1))
     (runLock aty2, doRootElim l2 (env `extLock` ()) recur2 (VDelayedKey var r2))

eqNF _ _ _ = False

eqNE :: Env -> Neutral -> Neutral -> Bool
-- eqNE size p1 p2 | traceShow ("eqNE: ", p1, p2) False = undefined
eqNE env (NVar i) (NVar j) = i == j
eqNE env (NApp f1 (Normal aty1 a1)) (NApp f2 (Normal aty2 a2)) =
  eqNE env f1 f2 && eqNF env (aty1, a1) (aty2, a2)
eqNE env (NRootElim _ a1 c1) (NRootElim _ a2 c2) =
  let var = makeVar env VTiny
  in case (c1 $$ var, c2 $$ var) of
    (VNeutral _ t1, VNeutral _ t2) -> eqNE (env `extVal` var) t1 t2
    _ -> error "Closure didn't contain a neutral"
eqNE _ _ _ = False

-- conv :: Env -> Val -> Val -> Bool
-- conv env t u = case (t, u) of
--   (VU, VU) -> True

--   (VPi _ a b, VPi _ a' b') ->
--        conv env a a'
--     && conv (env + 1) (b $$ VVar l) (b' $$ VVar l)

--   (VLam _ t, VLam _ t') ->
--     conv (env + 1) (t $$ VVar l) (t' $$ VVar l)

--   (VLam _ t, u) ->
--     conv (env + 1) (t $$ VVar l) (VApp u (VVar l))
--   (u, VLam _ t) ->
--     conv (env + 1) (VApp u (VVar l)) (t $$ VVar l)

--   (VVar x  , VVar x'   ) -> x == x'
--   (VApp t u, VApp t' u') -> conv l t t' && conv l u u'

--   (VTiny, VTiny) -> True

--   _ -> False

-- Elaboration
--------------------------------------------------------------------------------

-- type of every variable in scope
type Types = [Either LockName (Name, VTy)]

-- | Elaboration context.
data Ctx = Ctx {env :: Env, types :: Types, lvl :: Lvl, pos :: SourcePos}
   -- "unzipped" Ctx definition, for performance reason (also for convenience)
  deriving (Show)

names :: Ctx -> [String]
names ctx = fmap (either id fst) (types ctx)

emptyCtx :: SourcePos -> Ctx
emptyCtx = Ctx (Env [] []) [] 0

-- | Extend Ctx with a bound variable.
bind :: Name -> VTy -> Ctx -> Ctx
bind x ~a (Ctx env types l pos) =
  Ctx (env `extVal` makeVar env a) (Right (x, a):types) (l + 1) pos

bindLock :: Name -> Ctx -> Ctx
bindLock x (Ctx (Env vs keys) types l pos) =
  Ctx (Env (EnvLock:vs) keys) (Left x:types) (l + 1) pos

-- | Extend Ctx with a definition.
define :: Name -> Val -> VTy -> Ctx -> Ctx
define x ~t ~a (Ctx env types l pos) =
  Ctx (env `extVal` t) (Right (x, a):types) (l + 1) pos

-- | Typechecking monad. We annotate the error with the current source position.
type M = Either (String, SourcePos)

report :: Ctx -> String -> M a
report ctx msg = Left (msg, pos ctx)

showVal :: Ctx -> VTy -> Val -> String
showVal ctx a v = prettyTm 0 (names ctx) (quote (env ctx) a v) []

-- bidirectional algorithm:
--   use check when the type is already known
--   use infer if the type is unknown
-- (original Hindley-Milner does not use bidirectionality)
-- (even if you don't strictly need bidir, it's faster and has better errors)

check :: Ctx -> Raw -> VTy -> M Tm
check ctx t a = traceShow (ctx, t, a) $ case (t, a) of
  -- setting the source pos
  (RSrcPos pos t, a) -> check (ctx {pos = pos}) t a

  -- checking Lam with Pi type (canonical checking case)
  -- (\x. t) : ((x : A) -> B)
  (RLam x t, VPi x' a b) ->
    Lam x <$> check (bind x a ctx) t (b $$ makeVar (env ctx) a)
              -- go under a binder as usual

  -- fall-through checking
  (RLet x a t u, a') -> do     -- let x : a = t in u
    a <- check ctx a VU
    let ~va = eval (env ctx) a
    t <- check ctx t va          -- (I need to check with a VTy)
    let ~vt = eval (env ctx) t
    u <- check (define x vt va ctx) u a'
    pure (Let x a t u)

  (RRootIntro x t, VRoot x' a) -> RootIntro <$> check (bindLock x ctx) t (runLock a)

  -- if the term is not checkable, we switch to infer (change of direction)
  _ -> do
    (t, tty) <- infer ctx t
    unless (eqTy (env ctx) tty a) $
     report ctx -- "type mismatch"
        (printf
            "type mismatch\n\nexpected type:\n\n  %s\n\ninferred type:\n\n  %s\n"
            (showVal ctx VU a) (showVal ctx VU tty))
    pure t

infer :: Ctx -> Raw -> M (Tm, VTy)
infer ctx r = traceShow (ctx, r) $ case r of
  RSrcPos pos t -> infer (ctx {pos = pos}) t

  RVar x -> do
    let go i [] = report ctx ("variable out of scope: " ++ x)
        go i (Left x' : tys) = go (i + 1) tys
        go i (Right (x', a):tys)
          | x == x'   = pure (Var i, a)
          | otherwise = go (i + 1) tys
    go 0 (types ctx)

  RU -> pure (U, VU)   -- U : U rule

  RApp t u -> do
    (t, tty) <- infer ctx t
    case tty of
      VPi _ a b -> do
        u <- check ctx u a
        pure (App t u, b $$ eval (env ctx) u)
      tty ->
        report ctx $ "Expected a function type, instead inferred:\n\n  " ++ "todo" -- showVal ctx tty

  RLam{} -> report ctx "Can't infer type for lambda expression"

  RPi x a b -> do
    a <- check ctx a VU
    b <- check (bind x (eval (env ctx) a) ctx) b VU
    pure (Pi x a b, VU)

  RLet x a t u -> do
    a <- check ctx a VU
    let ~va = eval (env ctx) a
    t <- check ctx t va
    let ~vt = eval (env ctx) t
    (u, uty) <- infer (define x vt va ctx) u
    pure (Let x a t u, uty)

  RTiny -> pure (Tiny, VU)

  RRoot l a -> do
    a <- check (bindLock l ctx) a VU
    pure (Root l a, VU)

  RRootElim x t -> do
    (t, tty) <- infer (bind x VTiny ctx) t
    case tty of
      VRoot _ a -> do
        pure (RootElim x t, applyUnit a)
      tty ->
        report ctx $ "Expected a root type, instead inferred:\n\n  " ++ "todo" -- showVal ctx tty

  RRootIntro{} -> report ctx "Can't infer type for unapp expression"

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
    Var (Ix x)                -> ((ns !! x)++)

    App t u                   -> par p appp $ go appp ns t . (' ':) . go atomp ns u

    Lam (fresh ns -> x) t     -> par p letp $ ("λ "++) . (x++) . goLam (x:ns) t where
                                   goLam ns (Lam (fresh ns -> x) t) =
                                     (' ':) . (x++) . goLam (x:ns) t
                                   goLam ns t =
                                     (". "++) . go letp ns t

    U                         -> ("U"++)

    Pi "_" a b                -> par p pip $ go appp ns a . (" → "++) . go pip ("_":ns) b

    Pi (fresh ns -> x) a b    -> par p pip $ piBind ns x a . goPi (x:ns) b where
                                   goPi ns (Pi "_" a b) =
                                     (" → "++) . go appp ns a . (" → "++) . go pip ("_":ns) b
                                   goPi ns (Pi (fresh ns -> x) a b) =
                                     piBind ns x a . goPi (x:ns) b
                                   goPi ns b =
                                     (" → "++) . go pip ns b

    Let (fresh ns -> x) a t u -> par p letp $ ("let "++) . (x++) . (" : "++) . go letp ns a
                                 . ("\n    = "++) . go letp ns t . ("\nin\n"++) . go letp (x:ns) u

    Key u t -> par p pip $ ("key " ++) . go pip ns u . (" " ++) . go pip ns t
    Tiny                      -> ("T"++)
    Root (fresh ns -> x) a -> par p pip $ ("√ " ++) . (x++) . (". "++) . go pip ns a
    RootIntro t -> par p pip $ ("rintro " ++) . go pip ns t
    RootElim (fresh ns -> x) t -> par p letp $ ("relim "++) . (x++) . (". "++) . go letp (x:ns) t

instance Show Tm where showsPrec p = prettyTm p []

-- parsing
--------------------------------------------------------------------------------

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

keyword :: String -> Bool
keyword x = x == "let" || x == "in" || x == "λ" || x == "U" || x == "T" || x == "key" || x == "root" || x == "rintro" || x == "relim"

pIdent :: Parser Name
pIdent = try $ do
  x <- takeWhile1P Nothing isAlphaNum
  guard (not (keyword x))
  x <$ ws

pKeyword :: String -> Parser ()
pKeyword kw = do
  C.string kw
  (takeWhile1P Nothing isAlphaNum *> empty) <|> ws

pAtom :: Parser Raw
pAtom =
      withPos ((RVar <$> pIdent) <|> (RKey <$ symbol "key" <*> pure "L" <*> pAtom <*> pAtom) <|> (RU <$ symbol "U") <|> (RTiny <$ symbol "T"))
  <|> parens pRaw

pBinder = pIdent <|> symbol "_"
pSpine  = foldl1 RApp <$> some pAtom

pLam = do
  char 'λ' <|> char '\\'
  xs <- some pBinder
  char '.'
  t <- pRaw
  pure (foldr RLam t xs)

pRootIntro = do
  symbol "rintro"
  l <- pBinder
  char '.'
  t <- pRaw
  pure (RRootIntro l t)

pRootElim = do
  symbol "relim"
  xs <- some pBinder
  char '.'
  t <- pRaw
  pure (foldr RRootElim t xs)

pPi = do
  dom <- some (parens ((,) <$> some pBinder <*> (char ':' *> pRaw)))
  pArrow
  cod <- pRaw
  pure $ foldr (\(xs, a) t -> foldr (\x -> RPi x a) t xs) cod dom

pRoot = do
  symbol "root"
  l <- pBinder
  a <- pAtom
  pure $ RRoot l a

funOrSpine = do
  sp <- pSpine
  optional pArrow >>= \case
    Nothing -> pure sp
    Just _  -> RPi "_" sp <$> pRaw

pLet = do
  pKeyword "let"
  x <- pBinder
  symbol ":"
  a <- pRaw
  symbol "="
  t <- pRaw
  pKeyword "in"
  u <- pRaw
  pure $ RLet x a t u

pRaw = withPos (pLam <|> pRootElim <|> pRootIntro <|> pLet <|> pRoot <|> try pPi <|> funOrSpine)
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
  pure (tm, file)

-- main
--------------------------------------------------------------------------------

displayError :: String -> (String, SourcePos) -> IO ()
displayError file (msg, SourcePos path (unPos -> linum) (unPos -> colnum)) = do
  let lnum = show linum
      lpad = map (const ' ') lnum
  printf "%s:%d:%d:\n" path linum colnum
  printf "%s |\n"    lpad
  printf "%s | %s\n" lnum (lines file !! (linum - 1))
  printf "%s | %s\n" lpad (replicate (colnum - 1) ' ' ++ "^")
  printf "%s\n" msg

helpMsg = unlines [
  "usage: elabzoo-typecheck-closures-debruijn [--help|nf|type]",
  "  --help : display this message",
  "  nf     : read & typecheck expression from stdin, print its normal form and type",
  "  type   : read & typecheck expression from stdin, print its type"]

mainWith :: IO [String] -> IO (Raw, String) -> IO ()
mainWith getOpt getRaw = do
  getOpt >>= \case
    ["--help"] -> putStrLn helpMsg
    ["nf"]   -> do
      (t, file) <- getRaw
      traceShow t $ return ()
      case infer (emptyCtx (initialPos file)) t of
        Left err -> displayError file err
        Right (t, a) -> do
          print $ nf (Env [] []) a t
          putStrLn "  :"
          print $ quote (Env [] []) VU a
    ["type"] -> do
      (t, file) <- getRaw
      case infer (emptyCtx (initialPos file)) t of
        Left err     -> displayError file err
        Right (t, a) -> print $ quote (Env [] []) VU a
    _ -> putStrLn helpMsg

main :: IO ()
main = mainWith getArgs parseStdin

-- | Run main with inputs as function arguments.
main' :: String -> String -> IO ()
main' mode src = mainWith (pure [mode]) ((,src) <$> parseString src)
