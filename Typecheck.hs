module Typecheck where

import Prelude hiding (lookup)
import Data.List hiding (insert, sort, lookup)
import Data.Map (Map, empty, insert, lookup, keysSet)
import qualified Data.Map as Map
import qualified Data.Set as Set

import Core

-- Descriptive errors for type checking
data TypeCheckError
  = NoAxiom Sort | NoRule Sort Sort | NotInCtx String
  | NotAType Nf | NotASort Nf | NotAFunction Nf | NotOfType Nf Nf
  | NotEqType Nf Nf | NotASum Nf | NotASigma Nf | NotAPi Nf
  | NotAnArrow Nf | NotAnId Nf | NotAPair Nf | NotEqual Nf Nf
  | NotAWType Nf | NotAnApp Nf | CannotInfer Term

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
  show (NotAnArrow a)   = "Type " ++ show a ++ " is not an arrow type"
  show (NotAnId a)      = "Type " ++ show a ++ " is not an identity type"
  show (NotAPair t)     = "Term " ++ show t ++ " is not a pair"
  show (NotAnApp t)     = "Term " ++ show t ++ " is not an application"
  show (NotEqual s t)   = "Terms " ++ show s ++ " and " ++ show t ++ " are not equal "
  show (NotAWType t)    = "Term " ++ show t ++ " is not a W-type"
  show (CannotInfer a)  = "Cannot infer the type of " ++ show a

-- Convenience functions
asType :: Nf -> Nf -> Either TypeCheckError Sort
asType t (NfS s) = Right s
asType t _       = Left (NotAType t)

asSort :: Nf -> Either TypeCheckError Sort
asSort (NfS s) = Right s
asSort t       = Left (NotASort t)

asPi :: Nf -> Either TypeCheckError (String, Nf, Nf)
asPi (NfPi x a b) = Right (x, a, b)
asPi t            = Left (NotAPi t)

asApp :: Nf -> Either TypeCheckError (Ne, Nf)
asApp (NfNe (NeApp n t)) = Right (n, t)
asApp t                  = Left (NotAnApp t)

asArrow :: Nf -> Either TypeCheckError (Nf, Nf)
asArrow (NfPi x a b) = if x `notElem` freeVarsNf b
    then Right (a, b)
    else Left (NotAnArrow (NfPi x a b))
asArrow t = Left (NotAnArrow t)

asFun :: Nf -> Nf -> Either TypeCheckError (String, Nf, Nf)
asFun t (NfPi x a b) = Right (x, a, b)
asFun t _            = Left (NotAFunction t)

asArrowFun :: Nf -> Nf -> Either TypeCheckError (Nf, Nf)
asArrowFun t (NfPi "_" a b) = Right (a, b)
asArrowFun t (NfPi x a b)   =
  if x `notElem` freeVarsNf b
    then Right (a, b)
    else Left (NotAnArrow (NfPi x a b))
asArrowFun t _ = Left (NotAFunction t)

asWType :: Nf -> Either TypeCheckError (Nf, Nf)
asWType (NfW a b) = Right (a, b)
asWType t         = Left (NotAWType t)

asSum :: Nf -> Either TypeCheckError (Nf, Nf)
asSum (NfSum a b) = Right (a, b)
asSum t           = Left (NotASum t)

asSigma :: Nf -> Either TypeCheckError (String, Nf, Nf)
asSigma (NfSigma x a b) = Right (x, a, b)
asSigma t               = Left (NotASigma t)

asPair :: Nf -> Nf -> Either TypeCheckError (String, Nf, Nf)
asPair t (NfSigma x a b) = Right (x, a, b)
asPair t _               = Left (NotAPair t)

asPath :: Nf -> Either TypeCheckError (Nf, Nf, Nf)
asPath (NfId a s t) = Right (a, s, t)
asPath t            = Left (NotAnId t)

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

areEqual :: Nf -> Nf -> Either TypeCheckError ()
areEqual s t =
  if s == t
    then Right ()
    else Left (NotEqual s t)

getTypeNf :: Ctx -> Nf -> Either TypeCheckError Nf
getTypeNf ctx (NfNe n) = getTypeNe ctx n
getTypeNf ctx (NfS s) = case axioms s of
  Nothing -> Left (NoAxiom s)
  Just s' -> Right (NfS s')
getTypeNf ctx (NfLam x a t) = getTypeNf (insert x a ctx) t
getTypeNf ctx (NfPi x a b) = do
  s1 <- getTypeNf ctx a
  s1 <- asType a s1
  s2 <- getTypeNf (insert x a ctx) b
  s2 <- asType b s2
  case rules s1 s2 of
    Nothing -> Left (NoRule s1 s2)
    Just s  -> Right (NfS s)
getTypeNf ctx NfEmpty = Right (NfS (Type 0))
getTypeNf ctx (NfEmptyInd p) = do
  a         <- getTypeNf ctx p
  (x, a, b) <- asFun p a
  Right (NfPi x NfEmpty $ p @@ var x)
  where
    x = freeNameCtx "e" ctx
getTypeNf ctx NfUnit = Right (NfS (Type 0))
getTypeNf ctx NfTT = Right NfUnit
getTypeNf ctx (NfUnitInd p _) = do
  a         <- getTypeNf ctx p
  (x, a, b) <- asFun p a
  Right (NfPi x NfUnit $ p @@ var x)
  where
    x = freeNameCtx "u" ctx
getTypeNf ctx (NfSum a b) = do
  s1 <- getSortNf ctx a
  s2 <- getSortNf ctx b
  case rules s1 s2 of
    Nothing -> Left (NoRule s1 s2)
    Just s  -> Right (NfS s)
getTypeNf ctx (NfInl s b) = do
  a <- getTypeNf ctx s
  Right (NfSum a b)
getTypeNf ctx (NfInr t a) = do
  b <- getTypeNf ctx t
  Right (NfSum a b)
getTypeNf ctx (NfSumInd p _ _) = do
  a         <- getTypeNf ctx p
  (x, a, b) <- asFun p a
  Right (NfPi x a $ p @@ var x)
  where
    x = freeNameCtx "s" ctx
getTypeNf ctx (NfSigma x a b) = do
  s1 <- getTypeNf ctx a
  s1 <- asType a s1
  s2 <- getTypeNf (insert x a ctx) b
  s2 <- asType b s2
  case rules s1 s2 of
    Nothing -> Left (NoRule s1 s2)
    Just s  -> Right (NfS s)
getTypeNf ctx (NfPair x a b s t) = Right (NfSigma x a b)
getTypeNf ctx (NfFst x a b) = Right (NfSigma x a b ==> a)
getTypeNf ctx (NfSnd x a b) = 
    Right (NfPi v (NfSigma x a b) $
      substNf x (NfNe (NeFst x a b (NeV v))) b)
    where
    v = freeNameCtx "p" ctx
getTypeNf ctx (NfProdInd p _) = do
  a         <- getTypeNf ctx p
  (x, a, b) <- asFun p a
  Right (NfPi x a $ p @@ var x)
  where
    x = freeNameCtx "p" ctx
getTypeNf ctx NfNat = Right (NfS (Type 0))
getTypeNf ctx NfZero = Right NfNat
getTypeNf ctx (NfSuc _) = Right NfNat
getTypeNf ctx (NfNatInd p _ _) = do
  a         <- getTypeNf ctx p
  (x, a, b) <- asFun p a
  Right (NfPi x a $ p @@ var x)
  where
    x = freeNameCtx "n" ctx
getTypeNf ctx (NfId a _ _) = do
  s <- getSortNf ctx a
  Right (NfS s)
getTypeNf ctx (NfCong f p) = do
  p          <- getTypeNf ctx p
  (a, x, y)  <- asPath p
  t          <- getTypeNf ctx f
  (_, _, b)  <- asFun f t
  Right (NfId b (f @@ x) (f @@ y))
getTypeNf ctx (NfRefl t) = do
  a <- getTypeNf ctx t
  Right (NfId a t t)
getTypeNf ctx (NfSym p) = do
  t <- getTypeNf ctx p
  (a, x, y) <- asPath t
  Right (NfId a y x)
getTypeNf ctx (NfTrans p q) = do
  t <- getTypeNf ctx p
  (a, x, _) <- asPath t
  t <- getTypeNf ctx q
  (_, _, z) <- asPath t
  Right (NfId a x z)
getTypeNf ctx (NfW a b) = do
  s1        <- getSortNf ctx a
  t         <- getTypeNf ctx b
  (x, _, t) <- asFun b t
  s2        <- getSortNf ctx t
  case rules s1 s2 of
    Nothing -> Left (NoRule s1 s2)
    Just s  -> Right (NfS s)
getTypeNf ctx (NfSup a b s t) = Right (NfW a b)
getTypeNf ctx (NfWInd a b p f) = do
  a         <- getTypeNf ctx p
  (x, a, b) <- asFun p a
  Right (NfPi x a $ p @@ var x)
  where
    x = freeNameCtx "n" ctx
getTypeNf ctx (NfFunExt f g p) = do
  t <- getTypeNf ctx f
  Right (NfId t f g)

getTypeNe :: Ctx -> Ne -> Either TypeCheckError Nf
getTypeNe ctx (NeV x) = case lookup x ctx of
  Nothing -> Left (NotInCtx x)
  Just a  -> Right a
getTypeNe ctx (NeApp n t) = do
  t         <- getTypeNe ctx n
  (x, a, b) <- asFun (NfNe n) t
  Right (substNf x t b)
getTypeNe ctx (NeEmptyInd p n) = Right (p @@ NfNe n)
getTypeNe ctx (NeUnitInd p _ n) = Right (p @@ NfNe n)
getTypeNe ctx (NeSumInd p _ _ n) = Right (p @@ NfNe n)
getTypeNe ctx (NeProdInd p _ n) = Right (p @@ NfNe n)
getTypeNe ctx (NeNatInd p _ _ n) = Right (p @@ NfNe n)
getTypeNe ctx (NeFst x a b n) = Right a
getTypeNe ctx (NeSnd x a b n) = Right (substNf x (NfNe (NeFst x a b n)) b)
getTypeNe ctx (NeWInd a b p f n) = Right (p @@ NfNe n)

getSortNf :: Ctx -> Nf -> Either TypeCheckError Sort
getSortNf ctx (NfNe n) = getSortNe ctx n
getSortNf ctx (NfS s) = case axioms s of
  Nothing -> Left (NoAxiom s)
  Just s' -> Right s'
getSortNf ctx (NfPi x a b) = do
  s1 <- getSortNf ctx a
  s2 <- getSortNf (insert x a ctx) b
  case rules s1 s2 of
    Nothing -> Left (NoRule s1 s2)
    Just s  -> Right s
getSortNf ctx (NfSum a b) = do
  s1 <- getSortNf ctx a
  s2 <- getSortNf ctx b
  case rules s1 s2 of
    Nothing -> Left (NoRule s1 s2)
    Just s  -> Right s
getSortNf ctx (NfSigma x a b) = do
  s1 <- getSortNf ctx a
  s2 <- getSortNf (insert x a ctx) b
  case rules s1 s2 of
    Nothing -> Left (NoRule s1 s2)
    Just s  -> Right s
getSortNf ctx NfEmpty = Right (Type 0)
getSortNf ctx NfUnit = Right (Type 0)
getSortNf ctx NfNat = Right (Type 0)
getSortNf ctx (NfId a s t) = getSortNf ctx a
getSortNf ctx (NfW a b) = do
  s1 <- getSortNf ctx a
  s2 <- getSortNf ctx b
  case rules s1 s2 of
    Nothing -> Left (NoRule s1 s2)
    Just s  -> Right s
getSortNf ctx t = Left (NotAType t)

getSortNe :: Ctx -> Ne -> Either TypeCheckError Sort
getSortNe ctx (NeV x) = case lookup x ctx of
  Nothing      -> Left (NotInCtx x)
  Just (NfS s) -> Right s
  Just _       -> Left (NotAType (NfNe (NeV x)))
getSortNe ctx (NeApp n _) = do
  a         <- getTypeNe ctx n
  (x, a, b) <- asFun (NfNe n) a
  asSort b
getSortNe ctx (NeEmptyInd p _) = do
  a         <- getTypeNf ctx p
  (x, a, b) <- asFun p a
  asSort b
getSortNe ctx (NeUnitInd p _ _) = do
  a         <- getTypeNf ctx p
  (x, a, b) <- asFun p a
  asSort b
getSortNe ctx (NeSumInd p _ _ _) = do
  a         <- getTypeNf ctx p
  (x, a, b) <- asFun p a
  asSort b
getSortNe ctx (NeProdInd p _ _) = do
  a         <- getTypeNf ctx p
  (x, a, b) <- asFun p a
  asSort b
getSortNe ctx (NeNatInd p _ _ _) = do
  a         <- getTypeNf ctx p
  (x, a, b) <- asFun p a
  asSort b
getSortNe ctx (NeFst x a b n) = asSort a
getSortNe ctx (NeSnd x a b n) = asSort b
getSortNe ctx (NeWInd a b p _ _) = do
  a         <- getTypeNf ctx p
  (x, a, b) <- asFun p a
  asSort b

{-
Combined type inference and normalizer
If
  infer env ctx e == Right (v, a)
then
  ctx ⊢ e[env] : a
and
  e[env] => v
-}
infer :: Env -> Ctx -> Term -> Either TypeCheckError (Nf, Nf)
infer env ctx (S s) = case axioms s of
  Just s2 -> Right (NfS s, NfS s2)
  Nothing -> Left (NoAxiom s)
infer env ctx (V x) = case lookup x ctx of
  Just a  -> Right (NfNe (NeV x), a)
  Nothing -> case lookup x env of
    Just (t, a) -> Right (t, a)
    Nothing     -> Left (NotInCtx x)
infer env ctx (Pi x a b) = do
  -- C ⊢ A : Type i
  (a, s1) <- infer env ctx a
  s1      <- asType a s1
  -- C, x : A ⊢ B : Type j
  (b, s2) <- infer env (insert x a ctx) b
  s2      <- asType b s2
  case rules s1 s2 of
    -- C ⊢ (x : A) -> B : Type (max i j)
    Just s  -> Right (NfPi x a b, NfS s)
    Nothing -> Left (NoRule s1 s2)
infer env ctx (Lam x (Just a) t) = do
  -- C ⊢ A : Type i
  (a, s1) <- infer env ctx a
  s1      <- asType a s1
  -- C, x : A ⊢ t : B
  (t, b)  <- infer env (insert x a ctx) t
  -- C ⊢ \(x : A).t : (x : A) -> B
  Right (NfLam x a t, NfPi x a b)
infer env ctx (App f t) = do
  -- C ⊢ f : (x : A) -> B
  (f, p)    <- infer env ctx f
  (x, a, b) <- asFun f p
   -- C ⊢ t : A
  t         <- check env ctx t a
  -- C ⊢ f t : B[t/x]
  Right (f @@ t, substNf x t b)
infer env ctx Empty = Right (NfEmpty, type0) -- C ⊢ Empty : Type 0
infer env ctx (EmptyInd (Just p)) = do
  -- C ⊢ P : Empty -> Type i
  (p, t)    <- infer env ctx p
  (_, a, s) <- asFun p t
  _         <- eqType a NfEmpty
  _         <- asSort s
  -- C ⊢ EmptyInd P : (e : Empty) -> P e
  e         <- return $ freeName "e" env ctx
  Right (NfEmptyInd p, NfPi e NfEmpty (p @@ var e))
infer env ctx Unit  = Right (NfUnit, type0) -- C ⊢ Unit : Type 0
infer env ctx TT    = Right (NfTT, NfUnit) -- C ⊢ tt : Unit
infer env ctx (UnitInd (Just p) ptt) = do
  -- C ⊢ P : Unit -> Type i
  (p, t)    <- infer env ctx p
  (_, a, s) <- asFun p t
  _         <- eqType a NfUnit
  _         <- asSort s
  -- C ⊢ Ptt : P tt
  ptt <- check env ctx ptt (p @@ NfTT)
  u   <- return $ freeName "u" env ctx
  -- C ⊢ UnitInd P Ptt : (u : Unit) -> P u
  Right (NfUnitInd p ptt, NfPi u NfUnit (p @@ var u))
infer env ctx (Sum a b) = do
  -- C ⊢ A : Type i
  (a, s1) <- infer env ctx a
  s1      <- asType a s1
  -- C ⊢ B : Type j
  (b, s2) <- infer env ctx b
  s2      <- asType b s2
  case rules s1 s2 of
    -- C ⊢ A + B : Type (max i j)
    Just s  -> Right (NfSum a b, NfS s)
    Nothing -> Left (NoRule s1 s2)
infer env ctx (Inl t (Just b)) = do
  -- C ⊢ t : A
  (t, a) <- infer env ctx t
  -- C ⊢ B : Type i
  (b, s) <- infer env ctx b
  s      <- asType b s
  -- C ⊢ inl t : A + B
  Right (NfInl t b, NfSum a b)
infer env ctx (Inr t (Just a)) = do
  -- C ⊢ t : B
  (t, b) <- infer env ctx t
  -- C ⊢ A : Type i
  (a, s) <- infer env ctx a
  s      <- asType a s
  -- C ⊢ inr t : A + B
  Right (NfInl t a, NfSum a b)
infer env ctx (SumInd (Just p) f g) = do
  -- C ⊢ P : A + B -> Type i
  (p, t)     <- infer env ctx p
  (_, t, s)  <- asFun p t
  (a, b)     <- asSum t
  _          <- asSort s
  -- C ⊢ f : (x : A) -> P (inl x)
  x <- return $ freeName "x" env ctx
  f <- check env ctx f (NfPi x a $ p @@ NfInl b (var x))
  g <- check env ctx g (NfPi x b $ p @@ NfInr a (var x))
  -- C ⊢ SumInd P f g : (s : A + B) -> P s
  Right (NfSumInd p f g, NfPi x (NfSum a b) (p @@ var x))
infer env ctx (Sigma x a b) = do
  -- C ⊢ A : Type i
  (a, s1) <- infer env ctx a
  s1      <- asType a s1
  -- C, x : A ⊢ B : Type j
  (b, s2) <- infer env (insert x a ctx) b
  s2      <- asType b s2
  case rules s1 s2 of
    -- C ⊢ [x : A] B : Type (max i j)
    Just s  -> Right (NfSigma x a b, NfS s)
    Nothing -> Left (NoRule s1 s2)
infer env ctx (Pair (Just (x, a, b)) s t) = do
  -- C ⊢ A : Type i
  (a, s1) <- infer env ctx a
  s1      <- asType a s1
  -- C, x : A ⊢ B : Type i
  (b, s2) <- infer env (insert x a ctx) b
  s2      <- asType b s2
  -- C ⊢ s : A
  s <- check env ctx s a
  -- C ⊢ t : B[s/x]
  t <- check env ctx t (substNf x s b)
  -- C ⊢ (s,t) : [x : A] B
  Right (NfPair x a b s t, NfSigma x a b)
infer env ctx (Pair Nothing s t) = do
  -- C ⊢ s : A
  (s, a) <- infer env ctx s
  -- C ⊢ t : B
  (t, b) <- infer env ctx t
  -- C ⊢ (s,t) : A * B
  Right (NfPair "_" a b s t, NfSigma "_" a b)
infer env ctx (ProdInd (Just p) f) = do
  -- C ⊢ P : [x : A] B -> Type i
  (p, t)     <- infer env ctx p
  (_, t, s)  <- asFun p t
  (x, a, b)  <- asSigma t
  _          <- asSort s
  -- C ⊢ f : (y : A) (z : B x) -> P (y,z)
  (f, t)     <- infer env ctx f
  (y, a', t) <- asFun f t
  _          <- eqType a' a
  (z, b', t) <- asPi t
  _          <- eqType b' (renameNf y x b)
  _          <- eqType t (p @@ NfPair x a b (var y) (var z))
  s          <- return $ freeName "s" env ctx
  -- C ⊢ ProdInd P f : (s : [x : A] B) -> P s
  Right (NfProdInd p f, NfPi s (NfSigma x a b) (p @@ var s))
infer env ctx (Fst Nothing p) = do
  (p, t)    <- infer env ctx p
  (x, a, b) <- asPair p t
  Right (NfFst x a b @@ p, a)
infer env ctx (Fst (Just (x, a, b)) p) = do
  (a, s1) <- infer env ctx a
  s1      <- asType a s1
  (b, s2) <- infer env (insert x a ctx) b
  s2      <- asType b s2
  p       <- check env ctx p (NfSigma x a b)
  Right (NfFst x a b @@ p, a)
infer env ctx (Snd Nothing p) = do
  (p, t)    <- infer env ctx p
  (x, a, b) <- asPair p t
  Right (NfSnd x a b @@ p, substNf x (NfFst x a b @@ p) b)
infer env ctx (Snd (Just (x, a, b)) p) = do
  (a, s1) <- infer env ctx a
  s1      <- asType a s1
  (b, s2) <- infer env (insert x a ctx) b
  s2      <- asType b s2
  p       <- check env ctx p (NfSigma x a b)
  Right (NfSnd x a b @@ p, substNf x (NfFst x a b @@ p) b)
infer env ctx Nat = Right (NfNat, type0) -- C ⊢ Nat : Type 0
infer env ctx Zero = Right (NfZero, NfNat) -- C ⊢ zero : Nat
infer env ctx (Suc n) = do
   -- C ⊢ n : Nat
  (n, a) <- infer env ctx n
  _      <- ofType n a NfNat
  -- C ⊢ suc n : Nat
  Right (NfSuc n, NfNat)
infer env ctx (NatInd (Just p) z s) = do
  -- C ⊢ P : Nat -> Type i
  (p, t)     <- infer env ctx p
  (_, t, s1) <- asFun p t
  _          <- eqType t NfNat
  _          <- asSort s1
  -- C ⊢ z : P zero
  (z, t)     <- infer env ctx z
  _          <- eqType t (p @@ NfZero)
  -- C ⊢ s : (x : Nat) -> P x -> P (suc x)
  (s, t)     <- infer env ctx s
  (x, b', t) <- asFun s t
  _          <- eqType b' NfNat
  _          <- eqType t (p @@ var x ==> p @@ NfSuc (var x))
  n          <- return $ freeName "n" env ctx
  -- C ⊢ NatInd P z s : (n : Nat) -> P n
  Right (NfNatInd p z s, NfPi n NfNat (p @@ var n))
infer env ctx (Id Nothing x y) = do
  -- C ⊢ x : A
  (x, a)  <- infer env ctx x
  -- C ⊢ A : Type i
  s <- getSortNf ctx a
  -- C ⊢ y : A
  y <- check env ctx y a
  -- C ⊢ x == y : Type i
  Right (NfId a x y, NfS s)
infer env ctx (Id (Just a) x y) = do
  -- C ⊢ A : Type i
  (a, s) <- infer env ctx a
  s      <- asType a s
  -- C ⊢ x : A
  x <- check env ctx x a
  -- C ⊢ y : A
  y <- check env ctx y a
  -- C ⊢ x == y : Type i
  Right (NfId a x y, NfS s)
infer env ctx (Cong f p) = do
  -- C ⊢ f : A -> B
  (f, t) <- infer env ctx f
  (a, b) <- asArrowFun f t
  -- C ⊢ p : x == y
  (p, t)     <- infer env ctx p
  (a', x, y) <- asPath t
  _          <- eqType a a'
  -- C ⊢ Cong f p : f x == f y
  Right (NfCong f p, NfId b (f @@ x) (f @@ y))
infer env ctx (Refl x) = do
  -- C ⊢ x : A
  (x, a) <- infer env ctx x
  -- C ⊢ Refl x : x == x
  Right (NfRefl x, NfId a x x)
infer env ctx (Sym p) = do
  -- C ⊢ p : x == y
  (p, t) <- infer env ctx p
  (a, x, y) <- asPath t
  -- C ⊢ Sym p : y == x
  Right (NfSym p, NfId a y x)
infer env ctx (Trans p q) = do
  -- C ⊢ p : x == y
  (p, t) <- infer env ctx p
  (a, x, y) <- asPath t
  -- C ⊢ q : y == z
  (q, t) <- infer env ctx q
  (_, y', z) <- asPath t
  _          <- areEqual y y'
  -- C ⊢ Trans p q : x == z
  Right (NfTrans p q, NfId a x z)
infer env ctx (W a b) = do
  -- C ⊢ A : Type i
  (a, s1) <- infer env ctx a
  s1      <- asType a s1
  -- C ⊢ B : A -> Type j
  (b, t)     <- infer env ctx b
  (_, a', s) <- asFun b t
  _          <- eqType a a'
  s2         <- asSort s
  -- C ⊢ W A B : Type (max i j)
  case rules s1 s2 of
    Nothing -> Left (NoRule s1 s2)
    Just s  -> Right (NfW a b, NfS s)
infer env ctx (Sup (Just (a,b)) x u) = do
  (a, s)     <- infer env ctx a
  _          <- asSort s
  (b, t)     <- infer env ctx b
  (_, a', s) <- asFun b t
  _          <- eqType a a'
  _          <- asSort s
  -- C ⊢ x : A
  x <- check env ctx x a
  -- C ⊢ u : B x -> W A B
  u <- check env ctx u (b @@ x ==> NfW a b)
  -- C ⊢ sup x u : W A B
  Right (NfSup a b x u, NfW a b)
infer env ctx (WInd (Just p) f) = do
  -- C ⊢ P : W A B -> Type i
  (p, t)      <- infer env ctx p
  (_, w, s1)  <- asFun p t
  s1          <- asSort s1
  (a, b)      <- asWType w
  -- C ⊢ f : (x : A) (u : B x -> W A B) -> ((b : B x) -> P (u b)) -> P (sup x u)
  (f, t)      <- infer env ctx f
  (x, a', t)  <- asFun f t
  _           <- eqType a' a
  (u, t1, t)  <- asPi t
  (_, bx, w') <- asPi t1
  _           <- eqType bx (b @@ var x)
  _           <- eqType w' w
  (t1, psup)     <- asArrow t
  (bV, bx, pub) <- asPi t1
  _             <- eqType bx (b @@ var x)
  _             <- eqType pub (p @@ (var u @@ var bV))
  _             <- eqType psup (p @@ NfSup a b (var x) (var u))
  wV          <- return $ freeName "w" env ctx
  -- C ⊢ WInd P f : (w : W A B) -> P w
  Right (NfWInd a b p f, NfPi wV (NfW a b) (p @@ var wV))
infer env ctx (FunExt Nothing p) = do
  -- C ⊢ p : (x : A) -> f x == g x
  (p, t)       <- infer env ctx p
  (x, a, t)    <- asFun p t
  (bx, fx, gx) <- asPath t
  f            <- return $ NfLam x a fx
  g            <- return $ NfLam x a gx
  -- C ⊢ p : FunExt f g p : f == g
  Right (NfFunExt f g p, NfId (NfPi x a bx) f g)
infer env ctx (FunExt (Just (f, g)) p) = do
  -- C ⊢ f : (x : A) -> B x
  (f, t)    <- infer env ctx f
  (x, a, b) <- asFun f t
  -- C ⊢ g : (x : A) -> B x
  g <- check env ctx g (NfPi x a b) 
  -- C ⊢ p : (x : A) -> f x == g x
  p <- check env ctx p (NfPi x a $ NfId b (f @@ var x) (g @@ var x))
  -- C ⊢ p : FunExt f g p : f == g
  Right (NfFunExt f g p, NfId (NfPi x a b) f g)
infer env ctx t = Left (CannotInfer t)

{-
Combined type checker and normalizer
If
  check env ctx e a == Right v
then
  ctx ⊢ e[env] : a
and
  e[env] => v
-}
check :: Env -> Ctx -> Term -> Nf -> Either TypeCheckError Nf
check env ctx (Lam x _ t) (NfPi y a b) = do
  -- C, x : A ⊢ t : B
  t <- check env (insert x a ctx) t (renameNf y x b)
  -- C ⊢ \(x : A).t : (x : A) -> B
  Right (NfLam x a t)
check env ctx (Pair _ s t) (NfSigma x a b) = do
  s <- check env ctx s a
  t <- check env ctx t (substNf x s b)
  Right (NfPair x a b s t)
check env ctx (Inl t _) (NfSum a b) = do
  -- C ⊢ t : A
  t <- check env ctx t a
  -- C ⊢ inl t : A + B
  Right (NfInl t b)
check env ctx (Inr t _) (NfSum a b) = do
  -- C ⊢ t : B
  t <- check env ctx t b
  -- C ⊢ inr t : A + B
  Right (NfInr t a)
check env ctx (Sup _ x u) (NfW a b) = do
  x <- check env ctx x a
  u <- check env ctx u (b @@ x ==> NfW a b)
  Right (NfSup a b x u)
check env ctx (EmptyInd _) (NfPi x NfEmpty px) = do
  -- C ⊢ EmptyInd : (x : Empty) -> P x
  Right (NfEmptyInd (NfLam x NfEmpty px))
check env ctx (UnitInd _ t) (NfPi x NfUnit px) = do
  -- C ⊢ t : P tt
  t <- check env ctx t (substNf x NfTT px)
  -- C ⊢ UnitInd t : (x : Unit) -> P x
  Right (NfUnitInd (NfLam x NfUnit px) t)
check env ctx (SumInd _ f g) (NfPi x (NfSum a b) px) = do
  -- C ⊢ f : (x : A) -> P (inl x)
  f <- check env ctx f (NfPi x a (substNf x (NfInl (var x) b) px))
  -- C ⊢ g : (x : B) -> P (inr x)
  g <- check env ctx g (NfPi x b (substNf x (NfInl (var x) a) px))
  -- C ⊢ SumInd f g : (x : A + B) -> P x
  Right (NfSumInd (NfLam x (NfSum a b) px) f g)
check env ctx (NatInd _ z s) (NfPi x NfNat px) = do
  xV <- return $ newName "x" (keysSet env `Set.union` keysSet ctx)
  -- C ⊢ z : P 0
  z <- check env ctx z (substNf x NfZero px)
  -- C ⊢ s : (x : Nat) -> P x -> P (suc x)
  s <- check env ctx s (NfPi xV NfNat $ substNf x (var xV) px ==> substNf x (NfSuc (var xV)) px)
  -- C ⊢ NatInd z s : (x : Nat) -> P x
  Right (NfNatInd (NfLam x NfNat px) z s)
check env ctx (WInd _ f) (NfPi x (NfW a b) px) = do
  -- C ⊢ f : (x : A) (u : B x -> W A B) -> ((b : B x) -> P (u b)) -> P (sup x u)
  xV <- return $ newName "x" (keysSet env `Set.union` keysSet ctx)
  uV <- return $ newName "u" (keysSet env `Set.union` keysSet ctx
    `Set.difference` Set.singleton xV)
  bV <- return $ newName "u" (keysSet env `Set.union` keysSet ctx
    `Set.difference` Set.singleton xV `Set.difference` Set.singleton uV)
  f <- check env ctx f
    (NfPi xV a $ NfPi uV (b @@ var xV ==> NfW a b) $
      (NfPi bV (b @@ var xV) $ substNf x (var uV @@ var bV) px) ==>
      substNf x (NfSup a b (var xV) (var uV)) px)
  -- C ⊢ WInd f : (x : W A B) -> P x
  Right (NfWInd a b (NfLam x (NfW a b) px) f)
check env ctx e a = do
  (s, t) <- infer env ctx e
  _      <- ofType s t a
  Right s
