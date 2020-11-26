{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

import Control.Applicative
import Control.Arrow(first,second)
import Data.Maybe
import Data.Char
import Data.List
import System.Environment
import Text.Earley
import Text.Earley.Mixfix
import qualified Data.HashSet as HS
import qualified Data.Map as Map
import Data.Kind (Type,Constraint)

import Core
import Typecheck

data Input
  = InpV String
  | InpApp [Input] Input
  | InpPi [([String], Input)] Input
  | InpLam [([String], Maybe Input)] Input
  | InpSig [([String], Input)] Input
  | InpProd [Input] Input
  | InpSum [Input] Input
  | InpInl Input | InpInr Input
  | InpArrow [Input] Input
  | InpEq Input Input
  | InpRefl Input
  | InpSym Input
  | InpTrans [Input] Input
  | InpCong Input Input
  | InpEmpty | InpAbsurd
  | InpUnit | InpTT | InpUnitInd Input
  | InpNat | InpZero | InpSuc Input | InpNatInd Input Input
  deriving (Eq,Show)

showAsc :: String -> String -> [([String], Input)] -> String
showAsc lp rp [] = ""
showAsc lp rp ((xs,a):asc) =
  lp ++ intercalate " " xs ++ " : " ++ show a ++ rp ++ showAsc lp rp asc

showArg :: [([String], Maybe Input)] -> String
showArg [] = ""
showArg ((xs,Nothing):arg) = intercalate " " xs ++ showArg arg
showArg ((xs,Just a):arg) = "(" ++ intercalate " " xs ++ " : " ++ show a ++ ")" ++ showArg arg

prettyPrint :: Input -> String
prettyPrint (InpV x)        = x
prettyPrint (InpPi asc b)   = showAsc "(" ")" asc ++ " → " ++ prettyPrint b
prettyPrint (InpLam arg b)  = "λ" ++ showArg arg ++ " → " ++ prettyPrint b
prettyPrint (InpSig asc b)  = showAsc "[" "]" asc ++ " " ++ prettyPrint b
prettyPrint (InpArrow as b) = intercalate " → " (map prettyPrint (as ++ [b]))
prettyPrint (InpProd as b)  = intercalate " * " (map prettyPrint (as ++ [b]))
prettyPrint (InpSum as b)   = intercalate " + " (map prettyPrint (as ++ [b]))
prettyPrint (InpApp as b)   = intercalate " " (map prettyPrint (as ++ [b]))
prettyPrint (InpEq a b)     = prettyPrint a ++ " == " ++ prettyPrint b
prettyPrint (InpRefl a)     = "refl (" ++ prettyPrint a ++ ")"
prettyPrint (InpSym p)      = "sym (" ++ prettyPrint p ++ ")"
prettyPrint (InpTrans p q)  = intercalate " >> " (map prettyPrint (p ++ [q]))
prettyPrint InpEmpty        = "⊥"
prettyPrint InpAbsurd       = "!"
prettyPrint InpUnit         = "⊤"
prettyPrint (InpUnitInd t)  = "UnitInd " ++ prettyPrint t
prettyPrint (InpInl t)  = "inl (" ++ prettyPrint t ++ ")"
prettyPrint (InpInr t)  = "inr (" ++ prettyPrint t ++ ")"
prettyPrint InpNat      = "Nat"
prettyPrint InpZero     = "0"
prettyPrint (InpSuc t)  = "suc (" ++ prettyPrint t ++ ")"
prettyPrint (InpNatInd s t)  = "NatInd (" ++ prettyPrint s ++ ") (" ++ prettyPrint s ++ ")"

data Nat = Z | S Nat

data SNat (n :: Nat) where
    SZ :: SNat Z
    SS :: SNat n -> SNat (S n)

data Fin (n :: Nat) where
  FZ :: Fin (S n)
  FS :: Fin n -> Fin (S n)

infixr 5 :::

data Vec (n :: Nat) a where
  VNil  :: Vec Z a
  (:::) :: a -> Vec n a -> Vec (S n) a

repeatN :: SNat n -> a -> Vec n a
repeatN SZ     x = VNil
repeatN (SS n) x = x ::: repeatN n x

instance Functor (Vec n) where
  fmap f VNil       = VNil
  fmap f (x ::: xs) = f x ::: fmap f xs

instance Foldable (Vec n) where
  foldMap f VNil       = mempty
  foldMap f (x ::: xs) = f x <> foldMap f xs

instance Traversable (Vec n) where
  sequenceA VNil       = pure VNil
  sequenceA (x ::: xs) = pure (:::) <*> x <*> sequenceA xs

type family ArrowN (n :: Nat) (a :: Type) (b :: Type) :: Type where
  ArrowN Z     a b = b
  ArrowN (S n) a b = a -> ArrowN n a b

-- (a -> ..[n].. -> a -> b) -> a**n -> b
uncurryN :: ArrowN n a b -> Vec n a -> b
uncurryN y VNil       = y
uncurryN f (x ::: xs) = uncurryN (f x) xs

-- (a**n -> b) -> a -> ..[n].. -> a -> b
curryN :: SNat n -> (Vec n a -> b) -> ArrowN n a b
curryN SZ     f = f VNil
curryN (SS n) f = \x -> curryN n (\xs -> f (x ::: xs))

-- (a -> ..[n].. -> a -> b) -> m a -> ..[n].. -> m a -> m b
fmapN :: Applicative f => ArrowN n a b -> Vec n (f a) -> f b
fmapN f xs = uncurryN f <$> sequenceA xs

builtin :: SNat n ->
           Prod r String String Input ->
           Prod r String String String ->
           ArrowN n Input Input ->
           Prod r String String Input
builtin n expr name f = name *> fmapN f (repeatN n expr)

reserved :: HS.HashSet String
reserved = HS.fromList $
  reflTokens ++ equalTokens ++ lambdaTokens ++ colonTokens ++
  arrowTokens ++ transTokens ++ zeroTokens ++ sucTokens ++ natTokens ++
  ["*", "+", "(", ")", "[", "]"]

paren :: Prod r String String t -> Prod r String String t
paren p = namedToken "(" *> p <* namedToken ")"

bracket :: Prod r String String t -> Prod r String String t
bracket p = namedToken "[" *> p <* namedToken "]"

ident :: Prod r String String String
ident = satisfy (not . (`HS.member` reserved))
        <?> "identifier"

tokens :: [String] -> Prod r String String String
tokens xs = foldr (<|>) empty $ namedToken <$> xs

equalTokens :: [String]
equalTokens = ["=="]

equal :: Prod r String String String
equal = tokens equalTokens

arrowTokens :: [String]
arrowTokens = ["->", "→"]

arrow :: Prod r String String String
arrow = tokens arrowTokens

lambdaTokens :: [String]
lambdaTokens = ["\\", "λ"]

lambda :: Prod r String String String
lambda = tokens lambdaTokens

reflTokens :: [String]
reflTokens = ["refl"]

refl :: Prod r String String String
refl = tokens reflTokens

symTokens :: [String]
symTokens = ["sym"]

sym :: Prod r String String String
sym = tokens symTokens

congTokens :: [String]
congTokens = ["cong"]

cong :: Prod r String String String
cong = tokens congTokens

colonTokens :: [String]
colonTokens = [":"]

colon :: Prod r String String String
colon = tokens colonTokens

absurdTokens :: [String]
absurdTokens = ["!"]

absurd :: Prod r String String String
absurd = tokens absurdTokens

emptyTokens :: [String]
emptyTokens = ["Empty", "⊥"]

emptyProd :: Prod r String String String
emptyProd = tokens emptyTokens

unitTokens :: [String]
unitTokens = ["Unit", "⊤"]

unitProd :: Prod r String String String
unitProd = tokens unitTokens

ttTokens :: [String]
ttTokens = ["tt"]

ttProd :: Prod r String String String
ttProd = tokens ttTokens

unitIndTokens :: [String]
unitIndTokens = ["UnitInd"]

unitIndProd :: Prod r String String String
unitIndProd = tokens unitIndTokens

inlTokens :: [String]
inlTokens = ["inl"]

inlProd :: Prod r String String String
inlProd = tokens inlTokens

inrTokens :: [String]
inrTokens = ["inr"]

inrProd :: Prod r String String String
inrProd = tokens inrTokens

transTokens :: [String]
transTokens = [">>", "∙"]

transProd :: Prod r String String String
transProd = tokens transTokens

natTokens :: [String]
natTokens = ["Nat"]

natProd :: Prod r String String String
natProd = tokens natTokens

zeroTokens :: [String]
zeroTokens = ["zero", "0"]

zeroProd :: Prod r String String String
zeroProd = tokens zeroTokens

sucTokens :: [String]
sucTokens = ["suc"]

sucProd :: Prod r String String String
sucProd = tokens sucTokens

natIndTokens :: [String]
natIndTokens = ["NatInd"]

natIndProd :: Prod r String String String
natIndProd = tokens natIndTokens

{-
(identifier) id  ::= [a-z,A-Z][a-z,A-Z,0-9]*
(ascription) asc ::= id+ ":" e
(arguments)  arg ::= "(" asc ")" | id+
(pi type)    pi  ::= ("(" asc ")")+ "->" e
(sigma type) sig ::= ("[" asc "]")+ e
(lambdas)    lam ::= "\" arg+ "->" e
(operations) op  ::= "+" | "*" | "->" | "=="
(expression) e   ::= pi | sig | lam | e e | e op e
-}

grammar :: Grammar r (Prod r String String Input)
grammar = mdo
  asc       <- rule $ (,) <$> some ident <* colon <*> expr
              <?> "ascription"
  piTy      <- rule $ InpPi <$> some (paren asc) <* arrow <*> expr
              <?> "pi type"
  sigTy     <- rule $ InpSig <$> some (bracket asc) <*> expr
              <?> "sigma type"
  lamArg    <- rule $  (,) <$> some ident <*> pure Nothing
              <|> second Just <$> paren asc
  lam       <- rule $ lambda *> (InpLam <$> some lamArg <* arrow <*> expr)
              <?> "lambda abstraction"
  app       <- rule $ InpApp <$> some expr <*> expr
              <?> "application"
  arrTy     <- rule $ InpArrow <$> some (expr <* arrow) <*> expr
              <?> "arrow type"
  prod      <- rule $ InpProd <$> some (expr <* namedToken "*") <*> expr
              <?> "product type"
  sum       <- rule $ InpSum <$> some (expr <* namedToken "+") <*> expr
              <?> "sum type"
  inlTm     <- rule $ builtin (SS SZ) expr inlProd InpInl
              <?> "inl"
  inrTm     <- rule $ builtin (SS SZ) expr inlProd InpInr
              <?> "inr"
  eq        <- rule $ InpEq <$> expr <* equal <*> expr
              <?> "identity type"
  reflTm    <- rule $ builtin (SS SZ) expr refl InpRefl
              <?> "reflexivity"
  symTm     <- rule $ builtin (SS SZ) expr sym InpSym
              <?> "symmetry"
  transTm   <- rule $ InpTrans <$> some (expr <* transProd) <*> expr
              <?> "transitivity"
  congTm    <- rule $ builtin (SS $ SS SZ) expr cong InpCong
              <?> "congruence"
  emptyTm   <- rule $ builtin SZ expr emptyProd InpEmpty
              <?> "empty"
  absurdTm  <- rule $ builtin SZ expr absurd InpAbsurd
              <?> "absurd"
  unitTm    <- rule $ builtin SZ expr unitProd InpUnit
              <?> "unit"
  ttTm      <- rule $ builtin SZ expr ttProd InpTT
              <?> "tt"
  unitIndTm <- rule $ builtin (SS SZ) expr unitIndProd InpUnitInd
              <?> "unitInd"
  natTy     <- rule $ builtin SZ expr natProd InpNat
              <?> "nat type"
  zeroTm    <- rule $ builtin SZ expr zeroProd InpZero
              <?> "zero"
  sucTm     <- rule $ builtin (SS SZ) expr sucProd InpSuc
              <?> "successor"
  natIndTm  <- rule $ builtin (SS $ SS SZ) expr natIndProd InpNatInd
              <?> "nat induction"
  expr <- rule
     $  piTy <|> sigTy <|> lam
    <|> prod <|> sum <|> arrTy <|> app <|> eq
    <|> reflTm <|> symTm <|> transTm <|> congTm
    <|> emptyTm <|> absurdTm
    <|> unitTm <|> ttTm <|> unitIndTm
    <|> inlTm <|> inrTm
    <|> natTy <|> zeroTm <|> sucTm <|> natIndTm
    <|> InpV <$> ident
    <|> paren expr
  return expr

tokenize :: String -> [String]
tokenize ""        = []
tokenize (' ':xs)  = tokenize xs
tokenize ('\n':xs) = tokenize xs
tokenize (x:xs)
  | x `HS.member` special = [x] : tokenize xs
  | otherwise             = (x:as) : tokenize bs
  where
    (as, bs) = break (`HS.member` special) xs
    special = HS.fromList "()[],\\ \n"

safeHead :: [a] -> Maybe a
safeHead []    = Nothing
safeHead (x:_) = Just x

safeTail :: [a] -> Maybe a
safeTail []       = Nothing
safeTail (x:[])   = Just x
safeTail (x:y:ys) = safeTail (y:ys)

precedence :: Input -> Int
precedence (InpV _)       = -2
precedence (InpApp _ _)   = -1
precedence (InpSym _)     = 0
precedence (InpRefl _)    = 1
precedence (InpTrans _ _) = 1
precedence (InpCong _ _)  = 1
precedence (InpSuc _)     = 1
precedence (InpEq _ _)    = 2
precedence (InpSum _ _)   = 3
precedence (InpArrow _ _) = 4
precedence (InpProd _ _)  = 5
precedence (InpSig _ _)   = 6
precedence (InpPi _ _)    = 7
precedence (InpLam _ _)   = 8
precedence _ = 9

whichParse :: Input -> Input -> Bool
whichParse (InpLam a b)   (InpLam a' b')   = whichParse b b'
whichParse (InpPi a b)    (InpPi a' b')    = whichParse b b'
whichParse (InpSig a b)   (InpSig a' b')   = whichParse b b'
whichParse (InpProd a b)  (InpProd a' b')  = whichParse b b'
whichParse (InpSum a b)   (InpSum a' b')   = whichParse b b'
whichParse (InpArrow a b) (InpArrow a' b') = whichParse b b'
whichParse (InpEq a b)    (InpEq a' b')    = whichParse b b'
whichParse (InpApp a b)   (InpApp a' b')   = whichParse b b'
whichParse (InpRefl a)    (InpRefl a')     = whichParse a a'
whichParse (InpTrans a b) (InpTrans a' b') = whichParse b b'
whichParse (InpSuc a)     (InpSuc a')      = whichParse a a'
whichParse s t = if precedence t >= precedence s then True else False

selectParse :: Input -> Input -> Input
selectParse s t = if whichParse s t then t else s

parseTerm :: String -> Either (Report String [String]) Input
parseTerm xs =
  let (ps,r) = fullParses (parser grammar) $ tokenize xs in
  case foldl (\m t -> Just $ maybe t (selectParse t) m) Nothing ps of
    Nothing -> Left r
    Just p  -> Right p

desugarPi :: [([String], Input)] -> Input -> Term
desugarPi [] b           = desugar b
desugarPi (([],a):asc) b = desugarPi asc b
desugarPi (((x:xs),a):asc) b = Pi x (desugar a) (desugarPi ((xs,a):asc) b)

desugarSig :: [([String], Input)] -> Input -> Term
desugarSig [] b           = desugar b
desugarSig (([],a):asc) b = desugarSig asc b
desugarSig (((x:xs),a):asc) b = Sigma x (desugar a) (desugarSig ((xs,a):asc) b)

desugarProd :: [Input] -> Input -> Term
desugarProd [] b     = desugar b
desugarProd (a:as) b = Sigma "_" (desugar a) (desugarProd as b)

desugarSum :: [Input] -> Input -> Term
desugarSum [] b     = desugar b
desugarSum (a:as) b = Sum (desugar a) (desugarSum as b)

desugarArrow :: [Input] -> Input -> Term
desugarArrow [] b     = desugar b
desugarArrow (a:as) b = Pi "_" (desugar a) (desugarArrow as b)

desugarLam :: [([String], Maybe Input)] -> Input -> Term
desugarLam [] b           = desugar b
desugarLam (([],a):asc) b = desugarLam asc b
desugarLam (((x:xs),Nothing):asc) b =
  Lam x Nothing (desugarLam ((xs,Nothing):asc) b)
desugarLam (((x:xs),Just a):asc) b =
  Lam x (Just (desugar a)) (desugarLam ((xs,Just a):asc) b)

desugarApp :: [Input] -> Input -> Term
desugarApp [] y     = desugar y
desugarApp (x:xs) y = App (desugar x) (desugarApp xs y)

desugarTrans :: [Input] -> Input -> Term
desugarTrans []     y = desugar y
desugarTrans (x:xs) y = Trans (desugar x) (desugarApp xs y)

desugarVar :: String -> Term
desugarVar "Type" = Sort (Type 0)
desugarVar x = V x

desugar :: Input -> Term
desugar (InpV x)       = desugarVar x
desugar (InpApp a b)   = desugarApp a b
desugar (InpPi a b)    = desugarPi a b
desugar (InpLam a b)   = desugarLam a b
desugar (InpSig a b)   = desugarSig a b
desugar (InpProd a b)  = desugarProd a b
desugar (InpSum a b)   = desugarSum a b
desugar (InpArrow a b) = desugarArrow a b
desugar (InpEq a b)    = Id Nothing (desugar a) (desugar b)
desugar (InpRefl a)    = Refl (desugar a)
desugar (InpSym p)     = Sym (desugar p)
desugar (InpTrans a b) = desugarTrans a b
desugar (InpCong f p)  = Cong (desugar f) (desugar p)
desugar InpEmpty       = Empty
desugar InpAbsurd      = EmptyInd Nothing
desugar InpUnit = Unit
desugar InpTT = TT
desugar InpNat = Nat
desugar InpZero = Zero
desugar (InpSuc n) = Suc (desugar n)
desugar (InpNatInd s t) = NatInd Nothing (desugar s) (desugar t)
desugar (InpUnitInd t) = UnitInd Nothing (desugar t)
desugar (InpInl t) = Inl (desugar t) Nothing
desugar (InpInr t) = Inr (desugar t) Nothing

{-
  | InpArrow [Input] Input
  | InpAbsurd

data Term
  = S Sort
  | V String
  | Pi String Term Term
  | Lam String (Maybe Term) Term
  | App Term Term
  | Empty | EmptyInd (Maybe Term)
  | Unit | TT | UnitInd (Maybe Term) Term
  | Sum Term Term | Inl Term (Maybe Term) | Inr Term (Maybe Term)
  | SumInd (Maybe Term) Term Term
  | Sigma String Term Term | Pair (Maybe (String,Term,Term)) Term Term
  | ProdInd (Maybe Term) Term | Fst (Maybe (String,Term,Term)) Term | Snd (Maybe (String,Term,Term)) Term
  | Nat | Zero | Suc Term
  | NatInd (Maybe Term) Term Term
  | Id (Maybe Term) Term Term
  | Cong Term Term | Refl Term | Sym Term | Trans Term Term
  | W Term Term | Sup (Maybe (Term,Term)) Term Term | WInd (Maybe Term) Term
  | FunExt (Maybe (Term,Term)) Term
  deriving (Eq, Show)
-}
main :: IO ()
main = do
  xs:_ <- getArgs
  print $ tokenize xs
  (ps, r) <- return $ fullParses (parser grammar) $ tokenize xs
  mapM_ print ps
  putStrLn ""
  print $ parseTerm xs
  putStrLn ""
  print $ desugar <$> parseTerm xs
  putStrLn ""
  print $ infer Map.empty Map.empty <$> desugar <$> parseTerm xs
  putStrLn ""
  print $ flip (check Map.empty Map.empty) (NfNat ==> NfNat) <$> desugar <$> parseTerm xs