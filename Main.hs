import Prelude hiding ((**))
import Data.Set (singleton)
import qualified Data.Set as Set
import Data.Map (Map, empty, insert, lookup, toList)
import qualified Data.Map as Map
import System.CPUTime
import Text.Printf

import Core
import Synthesis

timeIt :: Show a => IO a -> IO a
timeIt ioa = do
    (t, a) <- timeItT ioa
    printf "CPU time: %6.4fs\n" t
    return a

timeItT :: Show a => IO a -> IO (Double, a)
timeItT ioa = do
    t1 <- getCPUTime
    a  <- ioa
    print a
    t2 <- getCPUTime
    return (fromIntegral (t2-t1) * 1e-12, a)

-- (A B : Type) -> (A -> B) -> A -> B
applyTy :: Nf
applyTy =
  NfPi "A" type0 $
  NfPi "B" type0 $
  (var "A" ==> var "B") ==> var "A" ==> var "B"

constTm :: Nf -> Nf -> Nf
constTm a t = NfLam "_" a t

unitRec :: Nf -> Nf -> Nf
unitRec a t = NfUnitInd (constTm NfUnit a) t

{-
EqUnit : Unit -> Unit -> Type
EqUnit tt tt = Unit

EqUnit = UnitRec (UnitRec Unit)
-}
unitEq :: Nf
unitEq = unitRec (NfUnit ==> type0) (unitRec type0 NfUnit)

-- (x y : Unit) -> EqUnit x y
unitIsProp :: Nf
unitIsProp =
  NfPi "x" NfUnit $
  NfPi "y" NfUnit $
  unitEq @@ var "x" @@ var "y"

-- (A : Type) -> Empty -> A
emptyImpliesAny :: Nf
emptyImpliesAny = NfPi "A" type0 $ NfEmpty ==> var "A"

sumRec :: Nf -> Nf -> Nf -> Nf -> Nf -> Nf
sumRec a b p f g =
  NfSumInd (constTm (NfSum a b) p) f g

boolTy :: Nf
boolTy = NfSum NfUnit NfUnit

falseTm :: Nf
falseTm = NfInl NfTT NfUnit

trueTm :: Nf
trueTm = NfInr NfTT NfUnit

boolRec :: Nf -> Nf -> Nf -> Nf
boolRec p f g = sumRec NfUnit NfUnit p (constTm NfUnit f) (constTm NfUnit g)

{-
EqBool : Bool -> Bool -> Type
EqBool false false = Unit
EqBool false true  = Empty
EqBool true  false = Empty
EqBool true  true  = Unit

EqBool = BoolRec (BoolRec Unit Empty) (BoolRec Empty Unit)
-}
boolEq :: Nf
boolEq =
  boolRec (boolTy ==> type0)
  (boolRec type0 NfUnit NfEmpty)
  (boolRec type0 NfEmpty NfUnit)

{-
not : Bool -> Bool
not false = true
not true  = false

not = BoolRec true false
-}
notTm :: Nf
notTm = boolRec boolTy trueTm falseTm

{-
NotInvol = (x : Bool) -> Eq (not (not x)) x
-}
notInvolTy :: Nf
notInvolTy = 
  NfPi "x" boolTy $ boolEq @@ (notTm @@ (notTm @@ var "x")) @@ var "x"

{-
NatRec : (A : Type) -> A -> (Nat -> A -> A) -> Nat -> A
NatRec A z s = NatInd (\(_:Nat).A) z s
-}
natRec :: Nf -> Nf -> Nf -> Nf
natRec a z s = NfNatInd (NfLam "_" NfNat a) z s

{-
IdNat = NatRec Nat zero (\_ n.suc n)
-}
idNatTm :: Nf
idNatTm =
  natRec NfNat NfZero $
  NfLam "_" NfNat $ NfLam "n" NfNat $ NfSuc (var "n")

{-
IdNatEq = (n : Nat) -> Eq (IdNat2 n) n
-}
idNatEq :: Nf
idNatEq =
  NfPi "n" NfNat $
  eqNat @@ (idNatTm @@ var "n") @@ var "n"

{-
EqNat : Nat -> Nat -> Type
EqNat zero    zero    = Unit
EqNat zero    (suc n) = Empty
EqNat (suc m) zero    = Empty
EqNat (suc m) (suc n) = EqNat m n

EqNat = NatRec (NatRec Unit (\_.Empty)) (\f.NatRec Empty (\_.f))
-}
eqNat :: Nf
eqNat =
  natRec (NfNat ==> type0)
    (natRec type0 NfUnit (NfLam "_" NfNat $ NfLam "_" type0 $ NfEmpty)) $
    NfLam "_" NfNat $ NfLam "f" (NfNat ==> type0) $
      natRec type0 NfEmpty (NfLam "n" NfNat $ NfLam "_" type0 $ var "f" @@ var "n")

{-
plus : Nat -> Nat -> Nat
plus zero    n  = n
plus (suc m) n  = suc (plus m n)

plus = NatRec (\n.n) (\_ f n.suc (f n))
-}
plusTm :: Nf
plusTm =
  natRec (NfNat ==> NfNat)
    (NfLam "n" NfNat $ var "n") $
    NfLam "_" NfNat $
    NfLam "f" (NfNat ==> NfNat) $
    NfLam "n" NfNat $
    NfSuc (var "f" @@ var "n")

-- PlusZero = (n : Nat) -> n + 0 == n
plusZero :: Nf
plusZero =
  NfPi "n" NfNat $
  eqNat @@ (plusTm @@ var "n" @@ NfZero) @@ var "n"

-- (m n : Nat) -> Eq (plus m n) (plus n m)
{-
+-zero : (n : Nat) -> n == n + 0
+-zero 0       = refl 0
+-zero (suc n) = cong suc (+-zero n)

+-comm : (m n : Nat) -> m + n == n + m
+-comm 0       n = +-zero n
+-comm (suc m) n = 

suc m + n == n + suc m
suc (m + n) == n + suc m

+-comm m n : m + n == n + m

This cannot be proven in our 
-}
plusComm :: Nf
plusComm =
  NfPi "m" NfNat $
  NfPi "n" NfNat $
  eqNat @@ (plusTm @@ var "m" @@ var "n") @@ (plusTm @@ var "n" @@ var "m")


-- (m n k : Nat) -> Eq (plus m (plus n k)) (plus (plus m n) k)
plusAssoc :: Nf
plusAssoc =
  NfPi "m" NfNat $
  NfPi "n" NfNat $
  NfPi "k" NfNat $
  eqNat @@
    (plusTm @@ var "m" @@ (plusTm @@ var "n" @@ var "k")) @@
    (plusTm @@ (plusTm @@ var "m" @@ var "n") @@ var "k")

{-
double : Nat -> Nat
double zero    = zero
double (suc n) = suc (suc (double n))

double = NatRec (\n.n) (\m n.suc (suc n))
-}
doubleTm :: Nf
doubleTm =
  natRec NfNat
    NfZero $
    NfLam "m" NfNat $
    NfLam "n" NfNat $
    NfSuc (NfSuc (var "n"))

-- (A -> B) -> ~B -> ~A
contrapos :: Nf
contrapos =
  NfPi "A" type0 $
  NfPi "B" type0 $
  (var "A" ==> var "B") ==> (var "B" ==> NfEmpty) ==> var "A" ==> NfEmpty

-- (B -> C) -> (A -> B) -> A -> C
compose :: Nf
compose =
  NfPi "A" type0 $
  NfPi "B" type0 $
  NfPi "C" type0 $
  (var "B" ==> var "C") ==> (var "A" ==> var "B") ==> var "A" ==> var "C"
{-
(A : Type) (B : A -> Type) (C : (x : A) -> B cx -> Type) ->
((x : A) (y : B x) -> C x y) ->
(f : (x : A) -> B x) ->
(x : A) -> C x (f x)
-}
depCompose :: Nf
depCompose =
  NfPi "A" type0 $
  NfPi "B" (var "A" ==> type0) $
  NfPi "C" (NfPi "x" (var "A") $ var "B" @@ var "x" ==> type0) $
  (NfPi "x" (var "A") $ NfPi "y" (var "B" @@ var "x") $ var "C" @@ var "x" @@ var "y") ==>
  NfPi "g" (NfPi "x" (var "A") $ var "B" @@ var "x")
  (NfPi "x" (var "A") $ var "C" @@ var "x" @@ (var "g" @@ var "x"))

-- (A * B -> C) -> A -> B -> C
curryTy :: Nf
curryTy = 
  NfPi "A" type0 $
  NfPi "B" type0 $
  NfPi "C" type0 $
  (var "A" ** var "B" ==> var "C") ==> var "A" ==> var "B" ==> var "C"

-- (A -> B -> C) -> A * B -> C
uncurryTy :: Nf
uncurryTy = 
  NfPi "A" type0 $
  NfPi "B" type0 $
  NfPi "C" type0 $
  (var "A" ==> var "B" ==> var "C") ==> var "A" ** var "B" ==> var "C"

notTy :: Nf -> Nf
notTy a = a ==> NfEmpty

decTy :: Nf -> Nf
decTy a = NfSum a (notTy a)

-- (m n : Nat) -> Dec (m == n)
natDiscrete :: Nf
natDiscrete =
  NfPi "m" NfNat $
  NfPi "n" NfNat $
  decTy (eqNat @@ var "m" @@ var "n")

{-
isEven n = [k : Nat] (2 * k == n)
-}
isEven :: Nf -> Nf
isEven n = NfSigma "k" NfNat $ eqNat @@ (doubleTm @@ var "k") @@ n

{-
isOdd n = isEven n -> Empty
-}
isOdd :: Nf -> Nf
isOdd n = isEven n ==> NfEmpty

{-
isEvenPlusTwo = (n : Nat) -> isEven n -> isEven (suc (suc n))
-}
isEvenPlusTwo :: Nf
isEvenPlusTwo =
  NfPi "n" NfNat $
  isEven (var "n") ==> isEven (NfSuc $ NfSuc $ var "n")

numeral :: Int -> Nf
numeral 0 = NfZero
numeral i = NfSuc (numeral (i-1))

types :: [Nf]
types =
  [curryTy, uncurryTy, contrapos, compose, depCompose,
   notInvolTy, plusZero, natDiscrete, isEven (numeral 100),
   isEvenPlusTwo]

ctx :: Ctx
ctx = empty

doSynth :: Nf -> IO Nf
doSynth t = do
  putStrLn $ show (toList ctx) ++ " ⊢ ? : " ++ show t
  t <- timeIt (return $ head $ synthAll ctx t)
  putStrLn ""
  return t

main :: IO ()
main = do
  mapM_ doSynth $ types
  return ()
  -- putStrLn $ show (toList ctx) ++ " ⊢ ? : " ++ show typ ++ "\n"
  -- t <- timeIt (return $ head $ synthAll ctx typ)
  -- return ()
  -- head $ synthAll ctx typ
  -- mapM_ print $ synthUpto 100 ctx plusZeroTy
