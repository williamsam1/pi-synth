module Core where

import Prelude hiding (lookup)
import Control.Monad
import Data.Char
import Data.List hiding (insert, sort, lookup)
import Data.Map (Map, empty, insert, lookup, keysSet)
import qualified Data.Map as Map
import qualified Data.Set as Set

-- Data types --

-- Sorts
data Sort = Type Int deriving (Eq)

instance Show Sort where
  show (Type 0) = "Type"
  show (Type i) = "Type[" ++ show i ++ "]"

-- Leave axiom and rule checking generic in
-- case this needs to be changed
axioms :: Sort -> Maybe Sort
axioms (Type i) = Just (Type (i + 1))

rules :: Sort -> Sort -> Maybe Sort
rules (Type i) (Type j) = Just (Type (max i j))

-- Raw terms with partial type annotations
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

-- Normal-form terms with full type annotations
data Nf
  = NfNe Ne
  | NfS Sort
  | NfLam String Nf Nf | NfPi String Nf Nf
  | NfEmpty | NfEmptyInd Nf
  | NfUnit | NfTT | NfUnitInd Nf Nf
  | NfSum Nf Nf | NfInl Nf Nf | NfInr Nf Nf | NfSumInd Nf Nf Nf
  | NfSigma String Nf Nf | NfPair String Nf Nf Nf Nf
  | NfProdInd Nf Nf | NfFst String Nf Nf | NfSnd String Nf Nf
  | NfNat | NfZero | NfSuc Nf | NfNatInd Nf Nf Nf
  | NfW Nf Nf | NfSup Nf Nf Nf Nf | NfWInd Nf Nf Nf Nf
  | NfId Nf Nf Nf | NfCong Nf Nf | NfRefl Nf | NfSym Nf | NfTrans Nf Nf
  | NfFunExt Nf Nf Nf

-- Neutral terms with full type annotations
data Ne
  = NeV String
  | NeApp Ne Nf
  | NeEmptyInd Nf Ne
  | NeUnitInd Nf Nf Ne
  | NeSumInd Nf Nf Nf Ne
  | NeProdInd Nf Nf Ne | NeFst String Nf Nf Ne | NeSnd String Nf Nf Ne
  | NeNatInd Nf Nf Nf Ne
  | NeWInd Nf Nf Nf Nf Ne

type Renaming = Map String String

type Ctx = Map String Nf

type Env = Map String (Nf, Nf)

prod :: [(String, Nf)] -> Nf -> Nf
prod []         b = b
prod ((x,a):vs) b = NfPi x a (prod vs b)

lam :: [(String, Nf)] -> Nf -> Nf
lam []         b = b
lam ((x,a):vs) b = NfLam x a (lam vs b)

sig :: [(String, Nf)] -> Nf -> Nf
sig []         b = b
sig ((x,a):vs) b = NfSigma x a (sig vs b)

infixr 6 ==>
(==>) :: Nf -> Nf -> Nf
a ==> b = NfPi "_" a b

neg :: Nf -> Nf
neg a = a ==> NfEmpty

infixr 6 `arr`
arr :: Term -> Term -> Term
arr a b = Pi "_" a b

infixl 7 **
(**) :: Nf -> Nf -> Nf
a ** b = NfSigma "_" a b

infixl 8 ||
(||) :: Nf -> Nf -> Nf
a || b = NfSum a b

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
niceVar (NfId _ _ _)    = "p"
niceVar _               = "x"

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
needsParensNf p (NfPair _ _ _ _ _) = False
needsParensNf p (NfFst _ _ _) = False
needsParensNf p (NfSnd _ _ _) = False
needsParensNf InfixL (NfPi _ _ _)  = True
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
needsParensNf p (NfId _ _ _) = True
needsParensNf p (NfCong _ _) = True
needsParensNf p (NfRefl _) = False
needsParensNf p (NfSym _) = True
needsParensNf p (NfTrans _ _) = True
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
needsParensNe p (NeFst _ _ _ _) = True
needsParensNe p (NeSnd _ _ _ _) = True
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
showProd a b = withParensNf InfixL a ++ " * " ++ withParensNf Arg b

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
showNf (NfEmptyInd p) = "()" -- "absurd" -- "EmptyInd " ++ withParensNf Arg p
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
showNf (NfPair x a b s t) = "(" ++ show s ++ ", " ++ show t ++ ")"
showNf (NfFst _ _ _) = "fst"
showNf (NfSnd _ _ _) = "snd"
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
showNf (NfId a s t)  = withParensNf InfixL s ++ " == " ++ withParensNf Arg t
showNf (NfCong f p)  = --withParensNf InfixL f ++ " @ " ++ withParensNf Arg p
  "cong " ++ withParensNf Arg f ++ " " ++ withParensNf Arg p
showNf (NfRefl t)    = "refl" -- ++ withParensNf Arg t
showNf (NfSym p)     = "~ " ++ withParensNf Arg p
  -- "sym " ++ withParensNf Arg p
showNf (NfTrans p q) = withParensNf InfixL p ++ " ∙ " ++ withParensNf Arg q
  -- "trans " ++ withParensNf Arg p ++ " " ++ withParensNf Arg q
showNf (NfW a b) = "W " ++ withParensNf Arg a ++ " " ++ withParensNf Arg b
showNf (NfSup a b s t) = "sup " ++ withParensNf Arg s ++ " " ++ withParensNf Arg t
showNf (NfWInd a b p f) = "WInd " ++ withParensNf Arg f
showNf (NfFunExt f g p) =
  "FunExt " ++ withParensNf Arg f ++ " " ++ withParensNf Arg g ++ " " ++ withParensNf Arg p

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
showNe (NeFst _ _ _ n) = "fst " ++ withParensNe Arg n
showNe (NeSnd _ _ _ n) = "snd " ++ withParensNe Arg n
showNe (NeWInd a b p f w) =
  "WInd " ++ withParensNf Arg f ++ " " ++ withParensNe Arg w

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

-- Evaluation --

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
alphaEqRenNf r (NfPair x a b s t) (NfPair y a' b' s' t')
  | x == y    = alphaEqRenNf r a a' && alphaEqRenNf r b b' && alphaEqRenNf r s s' && alphaEqRenNf r t t'
  | otherwise = alphaEqRenNf r a a' && alphaEqRenNf (insert x y r) b b' && alphaEqRenNf r s s' && alphaEqRenNf r t t'
alphaEqRenNf r (NfFst x a s) (NfFst y b t)
  | not (alphaEqRenNf r a b) = False
  | x == y                   = alphaEqRenNf r s t
  | otherwise                = alphaEqRenNf (insert x y r) s t
alphaEqRenNf r (NfSnd x a s) (NfSnd y b t)
  | not (alphaEqRenNf r a b) = False
  | x == y                   = alphaEqRenNf r s t
  | otherwise                = alphaEqRenNf (insert x y r) s t
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
alphaEqRenNf r (NfId a s t) (NfId a' s' t') =
  alphaEqRenNf r a a' &&
  alphaEqRenNf r s s' &&
  alphaEqRenNf r t t'
alphaEqRenNf r (NfCong f p) (NfCong f' p') =
  alphaEqRenNf r f f' &&
  alphaEqRenNf r p p'
alphaEqRenNf r (NfRefl t) (NfRefl t') = alphaEqRenNf r t t'
alphaEqRenNf r (NfSym p) (NfSym p') = alphaEqRenNf r p p'
alphaEqRenNf r (NfTrans p q) (NfTrans p' q') =
  alphaEqRenNf r p p' &&
  alphaEqRenNf r q q'
alphaEqRenNf r (NfW a b) (NfTrans a' b') =
  alphaEqRenNf r a a' &&
  alphaEqRenNf r b b'
alphaEqRenNf r (NfSup a b x u) (NfSup a' b' x' u') =
  alphaEqRenNf r a a' &&
  alphaEqRenNf r b b' &&
  alphaEqRenNf r x x' &&
  alphaEqRenNf r u u'
alphaEqRenNf r (NfWInd a b p f) (NfWInd a' b' p' f') =
  alphaEqRenNf r a a' &&
  alphaEqRenNf r b b' &&
  alphaEqRenNf r p p' &&
  alphaEqRenNf r f f'
alphaEqRenNf r (NfFunExt f g p) (NfFunExt f' g' p') =
  alphaEqRenNf r f f' &&
  alphaEqRenNf r g g' &&
  alphaEqRenNf r p p'
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
alphaEqRenNe r (NeFst x a b n) (NeFst y a' b' n') = alphaEqRenNe r n n'
alphaEqRenNe r (NeSnd x a b n) (NeSnd y a' b' n') = alphaEqRenNe r n n'
alphaEqRenNe r (NeWInd a b p f n) (NeWInd a' b' p' f' n') =
  alphaEqRenNf r a a' &&
  alphaEqRenNf r b b' &&
  alphaEqRenNf r p p' &&
  alphaEqRenNf r f f' &&
  alphaEqRenNe r n n'
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
renameNf x y (NfPair z a b s t)
  | z == x    = NfPair z (renameNf x y a) b (renameNf x y s) (renameNf x y t)
  | otherwise = NfPair z (renameNf x y a) (renameNf x y b) (renameNf x y s) (renameNf x y t)
renameNf x y (NfFst z a b)
  | z == x    = NfFst z (renameNf x y a) b
  | otherwise = NfFst z (renameNf x y a) (renameNf x y b)
renameNf x y (NfSnd z a b)
  | z == x    = NfSnd z (renameNf x y a) b
  | otherwise = NfSnd z (renameNf x y a) (renameNf x y b)
renameNf x y (NfProdInd p f) = NfProdInd (renameNf x y p) (renameNf x y f)
renameNf x y NfNat = NfNat
renameNf x y NfZero = NfZero
renameNf x y (NfSuc n) = NfSuc (renameNf x y n)
renameNf x y (NfNatInd p z s) =
  NfNatInd (renameNf x y p) (renameNf x y z) (renameNf x y s)
renameNf x y (NfId a s t) = NfId (renameNf x y a) (renameNf x y s) (renameNf x y t)
renameNf x y (NfCong f p) = NfCong (renameNf x y f) (renameNf x y p)
renameNf x y (NfRefl t) = NfRefl (renameNf x y t)
renameNf x y (NfSym p) = NfSym (renameNf x y p)
renameNf x y (NfTrans p q) = NfTrans (renameNf x y p) (renameNf x y q)
renameNf x y (NfW a b) = NfW (renameNf x y a) (renameNf x y b)
renameNf x y (NfSup a b s t) =
  NfSup (renameNf x y a) (renameNf x y b) (renameNf x y s) (renameNf x y t)
renameNf x y (NfWInd a b p f) =
  NfWInd (renameNf x y a) (renameNf x y b) (renameNf x y p) (renameNf x y f)
renameNf x y (NfFunExt f g p) =
  NfFunExt (renameNf x y f) (renameNf x y g) (renameNf x y p)

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
renameNe x y (NeFst z a b n)
  | z == x    = NeFst z (renameNf x y a) b (renameNe x y n)
  | otherwise = NeFst z (renameNf x y a) (renameNf x y b) (renameNe x y n)
renameNe x y (NeSnd z a b n)
  | z == x    = NeSnd z (renameNf x y a) b (renameNe x y n)
  | otherwise = NeSnd z (renameNf x y a) (renameNf x y b) (renameNe x y n)
renameNe x y (NeWInd a b p f n) =
  NeWInd (renameNf x y a) (renameNf x y b) (renameNf x y p)
    (renameNf x y f) (renameNe x y n)

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
freeVarsNf (NfPair x a b s t) =
  freeVarsNf a `Set.union`
  (freeVarsNf b `Set.difference` Set.singleton x) `Set.union`
  freeVarsNf s `Set.union`
  freeVarsNf t
freeVarsNf (NfFst x a b) =
  freeVarsNf a `Set.union` (freeVarsNf b `Set.difference` Set.singleton x)
freeVarsNf (NfSnd x a b) =
  freeVarsNf a `Set.union` (freeVarsNf b `Set.difference` Set.singleton x)
freeVarsNf (NfProdInd p f) = freeVarsNf p `Set.union` freeVarsNf f
freeVarsNf (NfSuc n) = freeVarsNf n
freeVarsNf (NfNatInd p z s) =
  freeVarsNf p `Set.union`
  freeVarsNf z `Set.union`
  freeVarsNf s
freeVarsNf (NfId a s t) =
  freeVarsNf a `Set.union` freeVarsNf s `Set.union` freeVarsNf t
freeVarsNf (NfCong f t) = freeVarsNf f `Set.union` freeVarsNf t
freeVarsNf (NfRefl s) = freeVarsNf s
freeVarsNf (NfSym p) = freeVarsNf p
freeVarsNf (NfTrans p q) = freeVarsNf p `Set.union` freeVarsNf q
freeVarsNf (NfW a b) = freeVarsNf a `Set.union` freeVarsNf b
freeVarsNf (NfSup a b s t) =
  freeVarsNf a `Set.union`
  freeVarsNf b `Set.union`
  freeVarsNf s `Set.union`
  freeVarsNf t
freeVarsNf (NfWInd a b p f) = 
  freeVarsNf a `Set.union`
  freeVarsNf b `Set.union`
  freeVarsNf p `Set.union`
  freeVarsNf f
freeVarsNf (NfFunExt f g p) = 
  freeVarsNf f `Set.union`
  freeVarsNf g `Set.union`
  freeVarsNf p
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
freeVarsNe (NeFst x a b n) = freeVarsNe n
freeVarsNe (NeSnd x a b n) = freeVarsNe n
freeVarsNe (NeWInd a b p f n) = 
  freeVarsNf a `Set.union`
  freeVarsNf b `Set.union`
  freeVarsNf p `Set.union`
  freeVarsNf f `Set.union`
  freeVarsNe n

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
boundVarsNf (NfPair x a b s t) =
  Set.singleton x `Set.union`
  boundVarsNf a `Set.union`
  boundVarsNf b `Set.union`
  boundVarsNf s `Set.union`
  boundVarsNf t
boundVarsNf (NfFst x a b) = Set.singleton x `Set.union` boundVarsNf a `Set.union` boundVarsNf b
boundVarsNf (NfSnd x a b) = Set.singleton x `Set.union` boundVarsNf a `Set.union` boundVarsNf b
boundVarsNf (NfProdInd p f) = boundVarsNf p `Set.union` boundVarsNf f
boundVarsNf (NfSuc n) = boundVarsNf n
boundVarsNf (NfNatInd p z s) =
  boundVarsNf p `Set.union`
  boundVarsNf z `Set.union`
  boundVarsNf s
boundVarsNf (NfId a s t) =
  boundVarsNf a `Set.union` boundVarsNf s `Set.union` boundVarsNf t
boundVarsNf (NfCong f t) = boundVarsNf f `Set.union` boundVarsNf t
boundVarsNf (NfRefl s) = boundVarsNf s
boundVarsNf (NfSym p) = boundVarsNf p
boundVarsNf (NfTrans p q) = boundVarsNf p `Set.union` boundVarsNf q
boundVarsNf (NfW a b) = boundVarsNf a `Set.union` boundVarsNf b
boundVarsNf (NfSup a b s t) =
  boundVarsNf a `Set.union`
  boundVarsNf b `Set.union`
  boundVarsNf s `Set.union`
  boundVarsNf t
boundVarsNf (NfWInd a b p f) = 
  boundVarsNf a `Set.union`
  boundVarsNf b `Set.union`
  boundVarsNf p `Set.union`
  boundVarsNf f
boundVarsNf (NfFunExt f g p) = 
  boundVarsNf f `Set.union`
  boundVarsNf g `Set.union`
  boundVarsNf p
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
boundVarsNe (NeFst x a b n) = boundVarsNe n
boundVarsNe (NeSnd x a b n) = boundVarsNe n
boundVarsNe (NeWInd a b p f n) = 
  boundVarsNf a `Set.union`
  boundVarsNf b `Set.union`
  boundVarsNf p `Set.union`
  boundVarsNf f `Set.union`
  boundVarsNe n

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
substNf x v (NfPair y a b s t)
  | y == x       = NfPair y a b (substNf x v s) (substNf x v t)
  | y `elem` fv  =
    let y' = newName y fv
        a' = rec a
        b' = rec (renameNf y y' b) in
        NfPair y' a' b' (substNf x v s) (substNf x v t)
  | otherwise =
    let a' = rec a
        b' = rec b in
        NfPair y a' b' (substNf x v s) (substNf x v t)
  where
    fv = freeVarsNf v
    rec = substNf x v
substNf x v (NfFst y a b)
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
substNf x v (NfSnd y a b)
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
substNf x v (NfProdInd p f) = NfProdInd (substNf x v p) (substNf x v f)
substNf x v (NfSuc n)   = NfSuc (substNf x v n)
substNf x v (NfNatInd p z s) =
  NfNatInd (substNf x v p) (substNf x v z) (substNf x v s)
substNf x v (NfId a s t) = NfId (substNf x v a) (substNf x v s) (substNf x v t)
substNf x v (NfCong f t) = NfCong (substNf x v f) (substNf x v t)
substNf x v (NfRefl t) = NfRefl (substNf x v t)
substNf x v (NfSym p) = NfSym (substNf x v p)
substNf x v (NfTrans p q) = NfTrans (substNf x v p) (substNf x v q)
substNf x v (NfW a b) = NfW (substNf x v a) (substNf x v b)
substNf x v (NfSup a b s t) =
  NfSup (substNf x v a) (substNf x v b) (substNf x v s) (substNf x v t)
substNf x v (NfWInd a b p f) =
  NfWInd (substNf x v a) (substNf x v b) (substNf x v p) (substNf x v f)
substNf x v (NfFunExt f g p) =
  NfFunExt (substNf x v f) (substNf x v g) (substNf x v p)
substNf x v t = t

{-
NatInd p z s zero => z
NatInd p z s (suc t) => s t (NatInd p z s t)
-}
evalNatInd :: Nf -> Nf -> Nf -> Nf -> Nf
evalNatInd p z s (NfNe n)  = NfNe (NeNatInd p z s n)
evalNatInd p z s NfZero    = z
evalNatInd p z s (NfSuc t) = s @@ t @@ evalNatInd p z s t

{-
WInd a b p f (sup x u) => f x u (\b.WInd a b p f (u b))
-}
evalWInd :: Nf -> Nf -> Nf -> Nf -> Nf -> Nf
evalWInd a b p f (NfNe n)         = NfNe (NeWInd a b p f n)
evalWInd a b p f (NfSup _ _ x u)  =
  f @@ x @@ u @@ (NfLam "b" (NfW a b) $ NfWInd a b p f @@ (u @@ var "b"))

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
    NfPair _ _ _ s t -> f' @@ s @@ t
substNe x v (NeNatInd p z s n) =
  let p' = substNf x v p
      z' = substNf x v z
      s' = substNf x v s
      n' = substNe x v n in
      evalNatInd p' z' s' n'
substNe x v (NeFst y a b n) =
  case substNe x v n of
    NfPair _ _ _ s t -> s
    NfNe n           ->
      if y == x then NfNe (NeFst y a b n)
      else if y `elem` fv then
        let y' = newName y fv
            a' = rec a
            b' = rec (renameNf y y' b) in
            NfNe (NeFst y' a' b' n)
      else
        let a' = rec a
            b' = rec b in
            NfNe (NeFst y a' b' n)
  where
    fv = freeVarsNf v
    rec = substNf x v
substNe x v (NeSnd y a b n) =
  case substNe x v n of
    NfPair _ _ _ s t -> t
    NfNe n           ->
      if y == x then NfNe (NeSnd y a b n)
      else if y `elem` fv then
        let y' = newName y fv
            a' = rec a
            b' = rec (renameNf y y' b) in
            NfNe (NeSnd y' a' b' n)
      else
        let a' = rec a
            b' = rec b in
            NfNe (NeSnd y a' b' n)
  where
    fv = freeVarsNf v
    rec = substNf x v
substNe x v (NeWInd a b p f n) = evalWInd a b p f (substNe x v n)

-- Neutral form application evaluation
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
apply (NfProdInd p f) (NfPair _ _ _ s t) = f @@ s @@ t
apply (NfNatInd p z s) t = evalNatInd p z s t
apply (NfFst x a b ) (NfNe n) = NfNe (NeFst x a b n)
apply (NfFst x a b) (NfPair _ _ _ s t) = s
apply (NfSnd x a b) (NfNe n) = NfNe (NeSnd x a b n)
apply (NfSnd _ _ _) (NfPair _ _ _ s t) = t
apply (NfWInd a b p f) t = evalWInd a b p f t
apply s t = error ("Tried to apply a non-function term " ++ show s ++ " to " ++ show t)

infixl 7 @@
(@@) :: Nf -> Nf -> Nf
(@@) = apply
