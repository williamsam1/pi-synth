module Core where

import Prelude hiding (lookup)
import Control.Monad
import Data.Char
import Data.List hiding (insert, sort, lookup)
import Data.Map (Map, empty, insert, lookup, keysSet)
import qualified Data.Map as Map
import qualified Data.Set as Set

-- Data types --

data Sort = Type Int deriving (Eq)

instance Show Sort where
  show (Type 0) = "Type"
  show (Type i) = "Type[" ++ show i ++ "]"

axioms :: Sort -> Maybe Sort
axioms (Type i) = Just (Type (i + 1))

rules :: Sort -> Sort -> Maybe Sort
rules (Type i) (Type j) = Just (Type (max i j))

data Term
  = S Sort
  | V String
  | Pi String Term Term
  | Lam String Term Term
  | App Term Term
  | Empty | EmptyInd Term
  | Unit | TT | UnitInd Term Term
  | Sum Term Term | Inl Term Term | Inr Term Term
  | SumInd Term Term Term
  | Sigma String Term Term | Pair String Term Term Term
  | ProdInd Term Term | Fst Term | Snd Term
  | Nat | Zero | Suc Term
  | NatInd Term Term Term

data Nf
  = NfNe Ne
  | NfS Sort
  | NfLam String Nf Nf
  | NfPi String Nf Nf
  | NfEmpty | NfEmptyInd Nf
  | NfUnit | NfTT | NfUnitInd Nf Nf
  | NfSum Nf Nf | NfInl Nf Nf | NfInr Nf Nf
  | NfSumInd Nf Nf Nf
  | NfSigma String Nf Nf | NfPair Nf Nf
  | NfProdInd Nf Nf
  | NfNat | NfZero | NfSuc Nf
  | NfNatInd Nf Nf Nf

data Ne
  = NeV String
  | NeApp Ne Nf
  | NeEmptyInd Nf Ne
  | NeUnitInd Nf Nf Ne
  | NeSumInd Nf Nf Nf Ne
  | NeProdInd Nf Nf Ne
  | NeNatInd Nf Nf Nf Ne
  | NeFst Ne | NeSnd Ne

type Renaming = Map String String

type Ctx = Map String Nf

type Env = Map String (Nf, Nf)

infixr 6 ==>
(==>) :: Nf -> Nf -> Nf
a ==> b = NfPi "_" a b

infixl 7 **
(**) :: Nf -> Nf -> Nf
a ** b = NfSigma "_" a b

var :: String -> Nf
var = NfNe . NeV

type0 :: Nf
type0 = NfS (Type 0)

-- Pretty printing --

data Position = InfixL | InfixR | Arg deriving (Show, Eq)

-- Returns a nice variable name for abstraction over a type
niceVar  :: Nf -> String
niceVar (NfS _)         = "A"
niceVar (NfPi _ _ _)    = "f"
niceVar NfUnit          = "u"
niceVar (NfSum _ _)     = "s"
niceVar (NfSigma _ _ _) = "p"
niceVar NfNat           = "n"
niceVar (NfNe _)        = "x"
niceVar _ = "_"

needsParensNat :: Nf -> Bool
needsParensNat n =
  let (i, t) = numForm n in
  case t of
    Nothing -> False
    Just t  -> if i == 0
      then needsParensNf Arg t
      else True

needsParensNf :: Position -> Nf -> Bool
needsParensNf p (NfNe n)      = needsParensNe p n
needsParensNf p (NfLam _ _ _) = True
needsParensNf p (NfPair _ _) = False
needsParensNf InfixL (NfPi _ _ _)  = True -- x == "_" || x `notElem` freeVarsNf b
needsParensNf InfixL (NfSigma _ _ _) = True
needsParensNf InfixL (NfSuc n)     = needsParensNat (NfSuc n)
needsParensNf p (NfSum _ _)   = True
needsParensNf p (NfInl _ _)   = True
needsParensNf p (NfInr _ _)   = True
needsParensNf p (NfUnitInd _ _) = True
needsParensNf p (NfEmptyInd _) = False
needsParensNf p (NfSumInd _ _ _) = True
needsParensNf p (NfProdInd _ _) = True
needsParensNf p (NfNatInd _ _ _) = True
needsParensNf InfixL _             = False
needsParensNf InfixR _             = False
needsParensNf p    (NfS s)       = False
needsParensNf p    NfEmpty       = False
needsParensNf p    NfUnit        = False
needsParensNf p    NfTT          = False
needsParensNf p    NfNat         = False
needsParensNf p    NfZero        = False
needsParensNf Arg    (NfSuc n)     = needsParensNat (NfSuc n)
needsParensNf Arg    _             = True

needsParensNe :: Position -> Ne -> Bool
needsParensNe p (NeV _) = False
needsParensNe p (NeUnitInd _ _ _) = True
needsParensNe p (NeEmptyInd _ _) = True
needsParensNe p (NeSumInd _ _ _ _) = True
needsParensNe p (NeProdInd _ _ _) = True
needsParensNe p (NeNatInd _ _ _ _) = True
needsParensNe p (NeFst _) = True
needsParensNe p (NeSnd _) = True
needsParensNe InfixL _      = False
needsParensNe InfixR _      = False
needsParensNe Arg    _      = True

withParensNf :: Position -> Nf -> String
withParensNf p t
  | needsParensNf p t = "(" ++ showNf t ++ ")"
  | otherwise         = showNf t

withParensNe :: Position -> Ne -> String
withParensNe p t
  | needsParensNe p t = "(" ++ showNe t ++ ")"
  | otherwise         = showNe t

showLam :: String -> Nf -> Nf -> String
showLam x a t =
  "λ" ++ x ++ "." ++ showNf t
  -- "λ(" ++ x ++ ":" ++ showNf a ++ ")." ++ showNf t

showArrow :: Nf -> Nf -> String
showArrow a b = withParensNf InfixL a ++ " → " ++ withParensNf InfixR b

showPi :: String -> Nf -> Nf -> String
showPi x a b
  | x == "_"                 = showArrow a b
  | x `notElem` freeVarsNf b = showArrow a b
  | otherwise                = "Π(" ++ x ++ ":" ++ showNf a ++ ") " ++ showNf b

showProd :: Nf -> Nf -> String
showProd a b = withParensNf InfixL a ++ " * " ++ withParensNf InfixR b

showSig :: String -> Nf -> Nf -> String
showSig x a b
  | x == "_"                 = showProd a b
  | x `notElem` freeVarsNf b = showProd a b
  | otherwise                = "Σ[" ++ x ++ ":" ++ showNf a ++ "] " ++ showNf b

showApp :: Ne -> Nf -> String
showApp n t = withParensNe InfixL n ++ " " ++ withParensNf Arg t

numForm :: Nf -> (Int, Maybe Nf)
numForm NfZero    = (0, Nothing)
numForm (NfSuc n) = 
  let (i, t) = numForm n in
  (i + 1, t)
numForm t         = (0, Just t)

showNum :: Int -> Nf -> String
showNum 0 t = showNf t
showNum 1 t = "suc " ++ withParensNf Arg t
showNum i t = "suc (" ++ showNum (i-1) t ++ ")"

showNat :: Nf -> String
showNat n =
  let (i, t) = numForm n in
  case t of
    Nothing -> show i
    Just t  -> showNum i t

showNf :: Nf -> String
showNf (NfNe n)      = showNe n
showNf (NfS s)       = show s
showNf (NfLam x a t) = showLam x a t
showNf (NfPi x a b)  = showPi x a b
showNf NfEmpty       = "⊥"
showNf (NfEmptyInd p) = "absurd" -- "EmptyInd " ++ withParensNf Arg p
showNf NfUnit        = "⊤"
showNf NfTT          = "tt"
showNf (NfUnitInd p t) =
  "UnitInd " ++ withParensNf Arg t
  -- "UnitInd " ++
  -- withParensNf Arg p ++ " " ++
  -- withParensNf Arg t
showNf (NfSum a b)   = withParensNf InfixL a ++ " ⊎ " ++ withParensNf Arg b
showNf (NfInl t b)   = "inl " ++ withParensNf Arg t
showNf (NfInr t a)   = "inr " ++ withParensNf Arg t
showNf (NfSumInd p f g) =
  "SumInd " ++
  withParensNf Arg f ++ " " ++
  withParensNf Arg g
  -- "SumInd " ++
  -- withParensNf Arg p ++ " " ++
  -- withParensNf Arg f ++ " " ++
  -- withParensNf Arg g
showNf (NfSigma x a b) = showSig x a b
showNf (NfPair s t) = "(" ++ show s ++ ", " ++ show t ++ ")"
showNf (NfProdInd p f) =
  "ProdInd " ++
  withParensNf Arg f
showNf NfNat         = "Nat"
showNf NfZero        = showNat NfZero
showNf (NfSuc n)     = showNat (NfSuc n)
showNf (NfNatInd p z s) =
  "NatInd " ++
  withParensNf Arg z ++ " " ++
  withParensNf Arg s
  -- "NatInd " ++
  -- withParensNf Arg p ++ " " ++
  -- withParensNf Arg z
  -- withParensNf Arg s

showNe :: Ne -> String
showNe (NeV x)     = x
showNe (NeApp n t) = showApp n t
showNe (NeEmptyInd p n) =
  "absurd " ++ withParensNe Arg n
  -- "EmptyInd " ++
  -- withParensNf Arg p ++ " " ++
  -- withParensNe Arg n
showNe (NeUnitInd p t n) =
  "UnitInd " ++
  withParensNf Arg t ++ " " ++
  withParensNe Arg n
  -- "UnitInd " ++
  -- withParensNf Arg p ++ " " ++
  -- withParensNf Arg t ++ " " ++
  -- withParensNe Arg n
showNe (NeSumInd p f g n) =
  "SumInd " ++
  withParensNf Arg f ++ " " ++
  withParensNf Arg g ++ " " ++
  withParensNe Arg n
  -- "SumInd " ++
  -- withParensNf Arg p ++ " " ++
  -- withParensNf Arg f ++ " " ++
  -- withParensNf Arg g ++ " " ++
  -- withParensNe Arg n
showNe (NeProdInd p f n) =
  "Prod " ++
  withParensNf Arg f ++ " " ++
  withParensNe Arg n
showNe (NeNatInd p z s n) =
  "NatInd " ++
  withParensNf Arg z ++ " " ++
  withParensNf Arg s ++ " " ++
  withParensNe Arg n
  -- "NatInd " ++
  -- withParensNf Arg p ++ " " ++
  -- withParensNf Arg z ++ " " ++
  -- withParensNf Arg s ++ " " ++
  -- withParensNe Arg n
showNe (NeFst n) = "fst " ++ withParensNe Arg n
showNe (NeSnd n) = "snd " ++ withParensNe Arg n

instance Show Nf where
  show = showNf

instance Show Ne where
  show = showNe

showCtx :: Ctx -> String
showCtx ctx =
  if Map.size ctx == 0
    then "•"
    else intercalate ", " (Map.foldrWithKey f [] ctx)
  where
    f :: String -> Nf -> [String] -> [String]
    f x t xs = ("(" ++ x ++ " : " ++ show t ++ ")") : xs

-- Evaluation and type-checking --

-- Efficient testing of equivalence under renaming
alphaEqRenNf :: Renaming -> Nf -> Nf -> Bool
alphaEqRenNf r (NfNe n1) (NfNe n2) = alphaEqRenNe r n1 n2
alphaEqRenNf r (NfS s1) (NfS s2) = s1 == s2
alphaEqRenNf r (NfLam x a s) (NfLam y b t)
  | not (alphaEqRenNf r a b) = False
  | x == y                   = alphaEqRenNf r s t
  | otherwise                = alphaEqRenNf (insert x y r) s t
alphaEqRenNf r (NfPi x a s) (NfPi y b t)
  | not (alphaEqRenNf r a b) = False
  | x == y                   = alphaEqRenNf r s t
  | otherwise                = alphaEqRenNf (insert x y r) s t
alphaEqRenNf r NfEmpty NfEmpty = True
alphaEqRenNf r (NfEmptyInd p) (NfEmptyInd p') = alphaEqRenNf r p p'
alphaEqRenNf r NfUnit NfUnit = True
alphaEqRenNf r NfTT NfTT = True
alphaEqRenNf r (NfUnitInd p t) (NfUnitInd p' t') =
  alphaEqRenNf r p p' && alphaEqRenNf r t t'
alphaEqRenNf r (NfSum a b) (NfSum a' b') =
  alphaEqRenNf r a a' && alphaEqRenNf r b b'
alphaEqRenNf r (NfInl t b) (NfInl t' b') =
  alphaEqRenNf r t t' && alphaEqRenNf r b b'
alphaEqRenNf r (NfInr t a) (NfInr t' a') =
  alphaEqRenNf r t t' && alphaEqRenNf r a a'
alphaEqRenNf r (NfSumInd p f g) (NfSumInd p' f' g') =
  alphaEqRenNf r p p' &&
  alphaEqRenNf r f f' &&
  alphaEqRenNf r g g'
alphaEqRenNf r (NfSigma x a s) (NfSigma y b t)
  | not (alphaEqRenNf r a b) = False
  | x == y                   = alphaEqRenNf r s t
  | otherwise                = alphaEqRenNf (insert x y r) s t
alphaEqRenNf r (NfPair s t) (NfPair s' t') = alphaEqRenNf r s s' && alphaEqRenNf r t t'
alphaEqRenNf r (NfProdInd p f) (NfProdInd p' f') =
  alphaEqRenNf r p p' &&
  alphaEqRenNf r f f'
alphaEqRenNf r NfNat NfNat = True
alphaEqRenNf r NfZero NfZero = True
alphaEqRenNf r (NfSuc m) (NfSuc n) = alphaEqRenNf r m n
alphaEqRenNf r (NfNatInd p z s) (NfNatInd p' z' s') =
  alphaEqRenNf r p p' &&
  alphaEqRenNf r z z' &&
  alphaEqRenNf r s s'
alphaEqRenNf r _ _ = False

alphaEqRenNe :: Renaming -> Ne -> Ne -> Bool
alphaEqRenNe r (NeV x) (NeV y)
  | Just y' <- lookup x r = y' == y
  | otherwise             = x == y
alphaEqRenNe r (NeApp a b) (NeApp c d) = alphaEqRenNe r a c && alphaEqRenNf r b d
alphaEqRenNe r (NeUnitInd p t n) (NeUnitInd p' t' n') =
  alphaEqRenNf r p p' &&
  alphaEqRenNf r t t' &&
  alphaEqRenNe r n n'
alphaEqRenNe r (NeEmptyInd p n) (NeEmptyInd p' n') =
  alphaEqRenNf r p p' &&
  alphaEqRenNe r n n'
alphaEqRenNe r (NeSumInd p f g n) (NeSumInd p' f' g' n') =
  alphaEqRenNf r p p' &&
  alphaEqRenNf r f f' &&
  alphaEqRenNf r g g' &&
  alphaEqRenNe r n n'
alphaEqRenNe r (NeProdInd p f n) (NeProdInd p' f' n') =
  alphaEqRenNf r p p' &&
  alphaEqRenNf r f f' &&
  alphaEqRenNe r n n'
alphaEqRenNe r (NeNatInd p z s n) (NeNatInd p' z' s' n') =
  alphaEqRenNf r p p' &&
  alphaEqRenNf r z z' &&
  alphaEqRenNf r s s' &&
  alphaEqRenNe r n n'
alphaEqRenNe r (NeFst s) (NeFst s') = alphaEqRenNe r s s'
alphaEqRenNe r (NeSnd s) (NeSnd s') = alphaEqRenNe r s s'
alphaEqRenNe r _ _ = False

-- Alpha equivalence
instance Eq Nf where
  s == t = alphaEqRenNf empty s t

instance Eq Ne where
  s == t = alphaEqRenNe empty s t

renameNf :: String -> String -> Nf -> Nf
renameNf x y (NfNe n) = NfNe (renameNe x y n)
renameNf x y (NfS s) = NfS s
renameNf x y (NfLam z a t)
  | z == x    = NfLam z a t
  | otherwise = NfLam z (renameNf x y a) (renameNf x y t)
renameNf x y (NfPi z a b)
  | z == x    = NfPi z (renameNf x y a) b
  | otherwise = NfPi z (renameNf x y a) (renameNf x y b)
renameNf x y NfEmpty = NfEmpty
renameNf x y (NfEmptyInd p) = NfEmptyInd (renameNf x y p)
renameNf x y NfUnit = NfUnit
renameNf x y NfTT = NfTT
renameNf x y (NfUnitInd p t) = NfUnitInd (renameNf x y p) (renameNf x y t)
renameNf x y (NfSum a b) = NfSum (renameNf x y a) (renameNf x y b)
renameNf x y (NfInl t b) = NfInl (renameNf x y t) (renameNf x y b)
renameNf x y (NfInr t a) = NfInr (renameNf x y t) (renameNf x y a)
renameNf x y (NfSumInd p f g) =
  NfSumInd (renameNf x y p) (renameNf x y f) (renameNf x y g)
renameNf x y (NfSigma z a b)
  | z == x    = NfSigma z (renameNf x y a) b
  | otherwise = NfSigma z (renameNf x y a) (renameNf x y b)
renameNf x y (NfPair s t) = NfPair (renameNf x y s) (renameNf x y t)
renameNf x y (NfProdInd p f) = NfProdInd (renameNf x y p) (renameNf x y f)
renameNf x y NfNat = NfNat
renameNf x y NfZero = NfZero
renameNf x y (NfSuc n) = NfSuc (renameNf x y n)
renameNf x y (NfNatInd p z s) =
  NfNatInd (renameNf x y p) (renameNf x y z) (renameNf x y s)

renameNe :: String -> String -> Ne -> Ne
renameNe x y (NeV s)
  | s == x    = NeV y
  | otherwise = NeV s
renameNe x y (NeApp n t) = NeApp (renameNe x y n) (renameNf x y t)
renameNe x y (NeEmptyInd p n) =
  NeEmptyInd (renameNf x y p) (renameNe x y n)
renameNe x y (NeUnitInd p t n) =
  NeUnitInd (renameNf x y p) (renameNf x y t) (renameNe x y n)
renameNe x y (NeSumInd p f g n) =
  NeSumInd (renameNf x y p) (renameNf x y f) (renameNf x y g) (renameNe x y n)
renameNe x y (NeProdInd p f n) =
  NeProdInd (renameNf x y p) (renameNf x y f) (renameNe x y n)
renameNe x y (NeNatInd p z s n) =
  NeNatInd (renameNf x y p) (renameNf x y z) (renameNf x y s) (renameNe x y n)
renameNe x y (NeFst s) = NeFst (renameNe x y s)
renameNe x y (NeSnd s) = NeSnd (renameNe x y s)

freeVarsNf :: Nf -> Set.Set String
freeVarsNf (NfNe n) = freeVarsNe n
freeVarsNf (NfLam x a t) =
  freeVarsNf a `Set.union` (freeVarsNf t `Set.difference` Set.singleton x)
freeVarsNf (NfPi x a b) =
  freeVarsNf a `Set.union` (freeVarsNf b `Set.difference` Set.singleton x)
freeVarsNf (NfEmptyInd p) = freeVarsNf p
freeVarsNf (NfUnitInd p t) = freeVarsNf p `Set.union` freeVarsNf t
freeVarsNf (NfSum a b) = freeVarsNf a `Set.union` freeVarsNf b
freeVarsNf (NfInl t b) = freeVarsNf t `Set.union` freeVarsNf b
freeVarsNf (NfInr t a) = freeVarsNf t `Set.union` freeVarsNf a
freeVarsNf (NfSumInd p f g) =
  freeVarsNf p `Set.union`
  freeVarsNf f `Set.union`
  freeVarsNf g
freeVarsNf (NfSigma x a b) =
  freeVarsNf a `Set.union` (freeVarsNf b `Set.difference` Set.singleton x)
freeVarsNf (NfPair s t) = freeVarsNf s `Set.union` freeVarsNf t
freeVarsNf (NfProdInd p f) = freeVarsNf p `Set.union` freeVarsNf f
freeVarsNf (NfSuc n) = freeVarsNf n
freeVarsNf (NfNatInd p z s) =
  freeVarsNf p `Set.union`
  freeVarsNf z `Set.union`
  freeVarsNf s
freeVarsNf _ = Set.empty

freeVarsNe :: Ne -> Set.Set String
freeVarsNe (NeV x)     = Set.singleton x
freeVarsNe (NeApp n t) = freeVarsNe n `Set.union` freeVarsNf t
freeVarsNe (NeEmptyInd p n) =
  freeVarsNf p `Set.union` freeVarsNe n
freeVarsNe (NeUnitInd p t n) =
  freeVarsNf p `Set.union`
  freeVarsNf t `Set.union`
  freeVarsNe n
freeVarsNe (NeSumInd p f g n) =
  freeVarsNf p `Set.union`
  freeVarsNf f `Set.union`
  freeVarsNf g `Set.union`
  freeVarsNe n
freeVarsNe (NeProdInd p f n) =
  freeVarsNf p `Set.union`
  freeVarsNf f `Set.union`
  freeVarsNe n
freeVarsNe (NeNatInd p z s n) =
  freeVarsNf p `Set.union`
  freeVarsNf z `Set.union`
  freeVarsNf s `Set.union`
  freeVarsNe n
freeVarsNe (NeFst n) = freeVarsNe n
freeVarsNe (NeSnd n) = freeVarsNe n

boundVarsNf :: Nf -> Set.Set String
boundVarsNf (NfNe n)      = boundVarsNe n
boundVarsNf (NfLam x a t) = Set.singleton x `Set.union` boundVarsNf a `Set.union` boundVarsNf t
boundVarsNf (NfPi x a b)  = Set.singleton x `Set.union` boundVarsNf a `Set.union` boundVarsNf b
boundVarsNf (NfEmptyInd p) = boundVarsNf p
boundVarsNf (NfUnitInd p t) = boundVarsNf p `Set.union` boundVarsNf t
boundVarsNf (NfSum a b) = boundVarsNf a `Set.union` boundVarsNf b
boundVarsNf (NfInl t b) = boundVarsNf t `Set.union` boundVarsNf b
boundVarsNf (NfInr t a) = boundVarsNf t `Set.union` boundVarsNf a
boundVarsNf (NfSumInd p f g) =
  boundVarsNf p `Set.union`
  boundVarsNf f `Set.union`
  boundVarsNf g
boundVarsNf (NfSigma x a b) = Set.singleton x `Set.union` boundVarsNf a `Set.union` boundVarsNf b
boundVarsNf (NfPair s t) = boundVarsNf s `Set.union` boundVarsNf t
boundVarsNf (NfProdInd p f) = boundVarsNf p `Set.union` boundVarsNf f
boundVarsNf (NfSuc n) = boundVarsNf n
boundVarsNf (NfNatInd p z s) =
  boundVarsNf p `Set.union`
  boundVarsNf z `Set.union`
  boundVarsNf s
boundVarsNf _ = Set.empty

boundVarsNe :: Ne -> Set.Set String
boundVarsNe (NeV x)     = Set.empty
boundVarsNe (NeApp n t) = boundVarsNe n `Set.union` boundVarsNf t
boundVarsNe (NeEmptyInd p n) =
  boundVarsNf p `Set.union` boundVarsNe n
boundVarsNe (NeUnitInd p t n) =
  boundVarsNf p `Set.union`
  boundVarsNf t `Set.union`
  boundVarsNe n
boundVarsNe (NeSumInd p f g n) =
  boundVarsNf p `Set.union`
  boundVarsNf f `Set.union`
  boundVarsNf g `Set.union`
  boundVarsNe n
boundVarsNe (NeProdInd p f n) =
  boundVarsNf p `Set.union`
  boundVarsNf f `Set.union`
  boundVarsNe n
boundVarsNe (NeNatInd p z s n) =
  boundVarsNf p `Set.union`
  boundVarsNf z `Set.union`
  boundVarsNf s `Set.union`
  boundVarsNe n
boundVarsNe (NeFst n) = boundVarsNe n
boundVarsNe (NeSnd n) = boundVarsNe n

-- Get unused variable name
newName :: String -> Set.Set String -> String
newName x ys = head $ [s ++ i | i <- "":(show <$> [0..]), s ++ i `notElem` ys]
  where
    s :: String
    s = dropWhileEnd isDigit x

-- Get unbound variable name
freeName :: String -> Env -> Ctx -> String
freeName x env ctx = newName x (keysSet env `Set.union` keysSet ctx)

freeNameCtx :: String -> Ctx -> String
freeNameCtx x ctx = newName x (keysSet ctx)

-- Substitution e[v/x]
substNf :: String -> Nf -> Nf -> Nf
substNf x v (NfNe n) = substNe x v n
substNf x v (NfLam y a t)
  | y == x       = NfLam y a t
  | y `elem` fv  =
    let y' = newName y fv
        a' = rec a
        t' = rec (renameNf y y' t) in
        NfLam y' a' t'
  | otherwise = do
    let a' = rec a
        t' = rec t in
        NfLam y a' t'
  where
    fv = freeVarsNf v
    rec = substNf x v
substNf x v (NfPi y a b)
  | y == x       = NfPi y a b
  | y `elem` fv  =
    let y' = newName y fv
        a' = rec a
        b' = rec (renameNf y y' b) in
        NfPi y' a' b'
  | otherwise =
    let a' = rec a
        b' = rec b in
        NfPi y a' b'
  where
    fv = freeVarsNf v
    rec = substNf x v
substNf x v (NfEmptyInd p) = NfEmptyInd (substNf x v p)
substNf x v (NfUnitInd p t) = NfUnitInd (substNf x v p) (substNf x v t)
substNf x v (NfSum a b) = NfSum (substNf x v a) (substNf x v b)
substNf x v (NfInl t b) = NfInl (substNf x v t) (substNf x v b)
substNf x v (NfInr t a) = NfInr (substNf x v t) (substNf x v a)
substNf x v (NfSumInd p f g) =
  NfSumInd (substNf x v p) (substNf x v f) (substNf x v g)
substNf x v (NfSigma y a b)
  | y == x       = NfSigma y a b
  | y `elem` fv  =
    let y' = newName y fv
        a' = rec a
        b' = rec (renameNf y y' b) in
        NfSigma y' a' b'
  | otherwise =
    let a' = rec a
        b' = rec b in
        NfSigma y a' b'
  where
    fv = freeVarsNf v
    rec = substNf x v
substNf x v (NfPair s t) = NfPair (substNf x v s) (substNf x v t)
substNf x v (NfProdInd p f) = NfProdInd (substNf x v p) (substNf x v f)
substNf x v (NfSuc n)   = NfSuc (substNf x v n)
substNf x v (NfNatInd p z s) =
  NfNatInd (substNf x v p) (substNf x v z) (substNf x v s)
substNf x v t = t

{-
NatInd p z s zero => z
NatInd p z s (suc t) => s t (NatInd p z s t)
-}
evalNatInd :: Nf -> Nf -> Nf -> Nf -> Nf
evalNatInd p z s (NfNe n)  = NfNe (NeNatInd p z s n)
evalNatInd p z s NfZero    = z
evalNatInd p z s (NfSuc t) = s @@ t @@ evalNatInd p z s t

substNe :: String -> Nf -> Ne -> Nf
substNe x v (NeV y)
  | y == x    = v
  | otherwise = NfNe (NeV y)
substNe x v (NeApp n t) =
  let n' = substNe x v n
      t' = substNf x v t in
      apply n' t'
substNe x v (NeEmptyInd p n) =
  let p' = substNf x v p
      n' = substNe x v n in
  case n' of
    NfNe n' -> NfNe (NeEmptyInd p' n')
substNe x v (NeUnitInd p t n) =
  let p' = substNf x v p
      t' = substNf x v t
      n' = substNe x v n in
  case n' of
    NfNe n' -> NfNe (NeUnitInd p' t' n')
    NfTT    -> t'
substNe x v (NeSumInd p f g n) =
  let p' = substNf x v p
      f' = substNf x v f
      g' = substNf x v g
      n' = substNe x v n in
  case n' of
    NfNe n'   -> NfNe (NeSumInd p' f' g' n')
    NfInl a _ -> f' @@ a
    NfInr b _ -> g' @@ b
substNe x v (NeProdInd p f n) =
  let p' = substNf x v p
      f' = substNf x v f
      n' = substNe x v n in
  case n' of
    NfNe n'    -> NfNe (NeProdInd p' f' n')
    NfPair s t -> f' @@ s @@ t
substNe x v (NeNatInd p z s n) =
  let p' = substNf x v p
      z' = substNf x v z
      s' = substNf x v s
      n' = substNe x v n in
      evalNatInd p' z' s' n'
substNe x v (NeFst n) =
  let n' = substNe x v n in
  case n' of
    NfNe n'    -> NfNe (NeFst n')
    NfPair s t -> s
substNe x v (NeSnd n) =
  let n' = substNe x v n in
  case n' of
    NfNe n'    -> NfNe (NeSnd n')
    NfPair s t -> t

-- Application evaluation
-- Fails if first argument is not really a function
-- or argument is not of correct type
apply :: Nf -> Nf -> Nf
apply (NfNe n) t = NfNe (NeApp n t)
apply (NfLam x a s) t = substNf x t s
apply (NfEmptyInd p) (NfNe n) = NfNe (NeEmptyInd p n)
apply (NfUnitInd p t) (NfNe n) = NfNe (NeUnitInd p t n)
apply (NfUnitInd p t) NfTT = t
apply (NfSumInd p f g) (NfNe n) = NfNe (NeSumInd p f g n)
apply (NfSumInd p f g) (NfInl a _) = f @@ a
apply (NfSumInd p f g) (NfInr b _) = g @@ b
apply (NfProdInd p f) (NfNe n) = NfNe (NeProdInd p f n)
apply (NfProdInd p f) (NfPair s t) = f @@ s @@ t
apply (NfNatInd p z s) t = evalNatInd p z s t

infixl 7 @@
(@@) :: Nf -> Nf -> Nf
(@@) = apply

data TypeCheckError
  = NoAxiom Sort
  | NoRule Sort Sort
  | NotInCtx String
  | NotAType Nf
  | NotASort Nf
  | NotAFunction Nf
  | NotOfType Nf Nf
  | NotEqType Nf Nf
  | NotASum Nf
  | NotASigma Nf
  | NotAPi Nf

instance Show TypeCheckError where
  show (NoAxiom s)      = "No axiom for the sort " ++ show s
  show (NoRule s1 s2)   = "No rule for the sorts " ++ show s1 ++ " " ++ show s2
  show (NotInCtx x)     = "Variable " ++ x ++ " is not in context"
  show (NotAType t)     = "Term " ++ show t ++ " is not a type"
  show (NotASort t)     = "Term " ++ show t ++ " is not a sort"
  show (NotAFunction t) = "Term " ++ show t ++ " is not a function"
  show (NotOfType t a)  = "Term " ++ show t ++ " is not of type " ++ show a
  show (NotEqType a b)  = "Type " ++ show a ++ " should be " ++ show b
  show (NotASum a)      = "Type " ++ show a ++ " is not a sum type"
  show (NotASigma a)    = "Type " ++ show a ++ " is not a sigma type"
  show (NotAPi a)       = "Type " ++ show a ++ " is not a pi type"

isType :: Nf -> Nf -> Either TypeCheckError Sort
isType t (NfS s) = Right s
isType t _       = Left (NotAType t)

isSort :: Nf -> Either TypeCheckError Sort
isSort (NfS s) = Right s
isSort t       = Left (NotASort t)

isPi :: Nf -> Either TypeCheckError (String, Nf, Nf)
isPi (NfPi x a b) = Right (x, a, b)
isPi t            = Left (NotAPi t)

asPi :: Nf -> Nf -> Either TypeCheckError (String, Nf, Nf)
asPi t (NfPi x a b) = Right (x, a, b)
asPi t _            = Left (NotAFunction t)

asSum :: Nf -> Either TypeCheckError (Nf, Nf)
asSum (NfSum a b) = Right (a, b)
asSum t           = Left (NotASum t)

asSigma :: Nf -> Either TypeCheckError (String, Nf, Nf)
asSigma (NfSigma x a b) = Right (x, a, b)
asSigma t               = Left (NotASigma t)

ofType :: Nf -> Nf -> Nf -> Either TypeCheckError ()
ofType t a b = 
  if a == b
    then Right ()
    else Left (NotOfType t b)

eqType :: Nf -> Nf -> Either TypeCheckError ()
eqType a b = 
  if a == b
    then Right ()
    else Left (NotEqType a b)

{-
Combined type-checker and normalizer
If
  eval env ctx e == Right (v, a)
then
  ctx ⊢ e[env] : a
and
  e[env] => v
-}
eval :: Env -> Ctx -> Term -> Either TypeCheckError (Nf, Nf)
eval env ctx (S s) = case axioms s of
  Just s2 -> Right (NfS s, NfS s2)
  Nothing -> Left (NoAxiom s)
eval env ctx (V x) = case lookup x ctx of
  Just a  -> Right (NfNe (NeV x), a)
  Nothing -> case lookup x env of
    Just (t, a) -> Right (t, a)
    Nothing     -> Left (NotInCtx x)
eval env ctx (Pi x a b) = do
  -- C ⊢ A : Type i
  (a, s1) <- eval env ctx a
  s1      <- isType a s1
  -- C, x : A ⊢ B : Type j
  (b, s2) <- eval env (insert x a ctx) b
  s2      <- isType b s2
  case rules s1 s2 of
    -- C ⊢ (x : A) -> B : Type (max i j)
    Just s  -> Right (NfPi x a b, NfS s)
    Nothing -> Left (NoRule s1 s2)
eval env ctx (Lam x a t) = do
  -- C ⊢ A : Type i
  (a, s1) <- eval env ctx a
  s1      <- isType a s1
  -- C, x : A ⊢ t : B
  (t, b)  <- eval env (insert x a ctx) t
  -- C ⊢ \(x : A).t : (x : A) -> B
  Right (NfLam x a t, NfPi x a b)
eval env ctx (App f t) = do
  -- C ⊢ f : (x : A) -> B
  (f, p)    <- eval env ctx f
  (x, a, b) <- asPi f p
   -- C ⊢ t : A
  (t, a')   <- eval env ctx t
  _         <- ofType t a' a
  -- C ⊢ f t : B[t/x]
  Right (f @@ t, substNf x t b)
eval env ctx Empty = Right (NfEmpty, type0) -- C ⊢ Empty : Type 0
eval env ctx (EmptyInd p) = do
  -- C ⊢ P : Empty -> Type i
  (p, t)    <- eval env ctx p
  (_, a, s) <- asPi p t
  _         <- eqType a NfEmpty
  _         <- isSort s
  -- C ⊢ EmptyInd P : (e : Empty) -> P e
  e         <- return $ freeName "e" env ctx
  Right (NfEmptyInd p, NfPi e NfEmpty (p @@ var e))
eval env ctx Unit  = Right (NfUnit, type0) -- C ⊢ Unit : Type 0
eval env ctx TT    = Right (NfTT, NfUnit) -- C ⊢ tt : Unit
eval env ctx (UnitInd p ptt) = do
  -- C ⊢ P : Unit -> Type i
  (p, t)    <- eval env ctx p
  (_, a, s) <- asPi p t
  _         <- eqType a NfUnit
  _         <- isSort s
  -- C ⊢ Ptt : P tt
  (ptt, t)  <- eval env ctx ptt
  _         <- ofType ptt t (p @@ NfTT)
  u         <- return $ freeName "u" env ctx
  -- C ⊢ UnitInd P Ptt : (u : Unit) -> P u
  Right (NfUnitInd p ptt, NfPi u NfUnit (p @@ var u))
eval env ctx (Sum a b) = do
  -- C ⊢ A : Type i
  (a, s1) <- eval env ctx a
  s1      <- isType a s1
  -- C ⊢ B : Type j
  (b, s2) <- eval env ctx b
  s2      <- isType b s2
  case rules s1 s2 of
    -- C ⊢ A + B : Type (max i j)
    Just s  -> Right (NfSum a b, NfS s)
    Nothing -> Left (NoRule s1 s2)
eval env ctx (Inl t b) = do
  -- C ⊢ t : A
  (t, a) <- eval env ctx t
  -- C ⊢ B : Type i
  (b, s) <- eval env ctx b
  s      <- isType b s
  -- C ⊢ inl t : A + B
  Right (NfInl t b, NfSum a b)
eval env ctx (Inr t a) = do
  -- C ⊢ t : B
  (t, b) <- eval env ctx t
  -- C ⊢ A : Type i
  (a, s) <- eval env ctx a
  s      <- isType a s
  -- C ⊢ inr t : A + B
  Right (NfInl t a, NfSum a b)
eval env ctx (SumInd p f g) = do
  -- C ⊢ P : A + B -> Type i
  (p, t)     <- eval env ctx p
  (_, t, s)  <- asPi p t
  (a, b)     <- asSum t
  _          <- isSort s
  -- C ⊢ f : (x : A) -> P (inl x)
  (f, t)     <- eval env ctx f
  (x, a', t) <- asPi f t
  _          <- eqType a' a
  _          <- eqType t (p @@ NfInl b (var x))
  -- C ⊢ g : (y : B) -> P (inr y)
  (g, t)     <- eval env ctx g
  (y, b', t) <- asPi f t
  _          <- eqType b' b
  _          <- eqType t (p @@ NfInl a (var y))
  s          <- return $ freeName "s" env ctx
  -- C ⊢ SumInd P f g : (s : A + B) -> P s
  Right (NfSumInd p f g, NfPi s (NfSum a b) (p @@ var s))
eval env ctx (Sigma x a b) = do
  -- C ⊢ A : Type i
  (a, s1) <- eval env ctx a
  s1      <- isType a s1
  -- C, x : A ⊢ B : Type j
  (b, s2) <- eval env (insert x a ctx) b
  s2      <- isType b s2
  case rules s1 s2 of
    -- C ⊢ [x : A] B : Type (max i j)
    Just s  -> Right (NfSigma x a b, NfS s)
    Nothing -> Left (NoRule s1 s2)
eval env ctx (Pair x b s t) = do
  -- C ⊢ s : A
  (s, a) <- eval env ctx s
  -- C, x : A ⊢ B : Type i
  (b, s2) <- eval env (insert x a ctx) b
  s2      <- isType b s2
  -- C ⊢ t : B[s/x]
  (t, bs) <- eval env ctx t
  _       <- ofType t bs (substNf x s b)
  -- C ⊢ (s,t) : [x : A] B
  Right (NfPair s t, NfSigma x a b)
eval env ctx (ProdInd p f) = do
  -- C ⊢ P : [x : A] B -> Type i
  (p, t)     <- eval env ctx p
  (_, t, s)  <- asPi p t
  (x, a, b)  <- asSigma t
  _          <- isSort s
  -- C ⊢ f : (y : A) (z : B x) -> P (y,z)
  (f, t)     <- eval env ctx f
  (y, a', t) <- asPi f t
  _          <- eqType a' a
  (z, b', t) <- isPi t
  _          <- eqType b' (renameNf y x b)
  _          <- eqType t (p @@ NfPair (var y) (var z))
  s          <- return $ freeName "s" env ctx
  -- C ⊢ ProdInd P f : (s : [x : A] B) -> P s
  Right (NfProdInd p f, NfPi s (NfSigma x a b) (p @@ var s))
eval env ctx Nat = Right (NfNat, type0) -- C ⊢ Nat : Type 0
eval env ctx Zero = Right (NfZero, NfNat) -- C ⊢ zero : Nat
eval env ctx (Suc n) = do
   -- C ⊢ n : Nat
  (n, a) <- eval env ctx n
  _      <- ofType n a NfNat
  -- C ⊢ suc n : Nat
  Right (NfSuc n, NfNat)
eval env ctx (NatInd p z s) = do
  -- C ⊢ P : Nat -> Type i
  (p, t)     <- eval env ctx p
  (_, t, s1) <- asPi p t
  _          <- eqType t NfNat
  _          <- isSort s1
  -- C ⊢ z : P zero
  (z, t)     <- eval env ctx z
  _          <- eqType t (p @@ NfZero)
  -- C ⊢ s : (x : Nat) -> P x -> P (suc x)
  (s, t)     <- eval env ctx s
  (x, b', t) <- asPi s t
  _          <- eqType b' NfNat
  _          <- eqType t (p @@ var x ==> p @@ NfSuc (var x))
  n          <- return $ freeName "n" env ctx
  -- C ⊢ NatInd P z s : (n : Nat) -> P n
  Right (NfNatInd p z s, NfPi n NfNat (p @@ var n))