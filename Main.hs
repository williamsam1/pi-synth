import Prelude hiding ((**), (||))
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

constTm :: Nf -> Nf -> Nf
constTm a t = NfLam "_" a t

unitRec :: Nf -> Nf -> Nf
unitRec a t = NfUnitInd (constTm NfUnit a) t

-- isProp A = (x y : A) -> x == y
isProp :: Nf -> Nf
isProp a = prod [("x", a), ("y", a)] $
  NfId a (var "x") (var "y")

-- isDec A = A + ~A
isDec :: Nf -> Nf
isDec a = a || neg a

-- isDiscrete A = (x y : A) -> isDec (x == y)
isDiscrete :: Nf -> Nf
isDiscrete a = prod [("x", a), ("y", a)] $ isDec (NfId a (var "x") (var "y"))

unitIsProp :: Nf
unitIsProp = isProp NfUnit

unitIsDiscrete :: Nf
unitIsDiscrete = isDiscrete NfUnit

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

notTm :: Nf
notTm = boolRec boolTy trueTm falseTm

andTm :: Nf
andTm =
  boolRec (boolTy ==> boolTy)
    (NfLam "x" boolTy $ falseTm)
    (NfLam "x" boolTy $ var "x")

orTm :: Nf
orTm =
  boolRec (boolTy ==> boolTy)
    (NfLam "x" boolTy $ var "x")
    (NfLam "x" boolTy $ trueTm)

data Lit      = Pos String | Neg String
type Disjunct = [Lit]
type Conjunct = [Disjunct]

lit :: Lit -> Nf
lit (Pos x) = var x
lit (Neg x) = notTm @@ var x

disjunct :: Disjunct -> Nf
disjunct []         = trueTm 
disjunct (l:[])     = lit l
disjunct (l1:l2:ls) = orTm @@ lit l1 @@ disjunct (l2:ls)

conjunct :: Conjunct -> Nf
conjunct []         = trueTm
conjunct (d:[])     = disjunct d
conjunct (d1:d2:ds) = andTm @@ disjunct d1 @@ conjunct (d2:ds)

litVars :: Lit -> Set.Set String
litVars (Pos x) = Set.singleton x
litVars (Neg x) = Set.singleton x

disVars :: Disjunct -> Set.Set String
disVars []     = Set.empty
disVars (l:ls) = litVars l `Set.union` disVars ls

conVars :: Conjunct -> Set.Set String
conVars []     = Set.empty
conVars (d:ds) = disVars d `Set.union` conVars ds

satTy :: Conjunct -> Nf
satTy e = prod [(x, boolTy) | x <- Set.toList $ conVars e] (conjunct e)

{-
NotInvol = (x : Bool) -> not (not x) == x
-}
notInvolTy :: Nf
notInvolTy =
  NfPi "x" boolTy $
  NfId boolTy (notTm @@ (notTm @@ var "x")) (var "x")

{-
NatRec : (A : Type) -> A -> (Nat -> A -> A) -> Nat -> A
NatRec A z s = NatInd (\(_:Nat).A) z s
-}
natRec :: Nf -> Nf -> Nf -> Nf
natRec a z s = NfNatInd (NfLam "_" NfNat a) z s

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
    lam [("m", NfNat), ("f", NfNat ==> NfNat), ("n", NfNat)] $
    NfSuc (var "f" @@ var "n")

-- plusZero = (n : Nat) -> n + 0 == n
plusZero :: Nf
plusZero =
  NfPi "n" NfNat $
  NfId NfNat (plusTm @@ var "n" @@ NfZero) (var "n")

-- plusComm : (m n : Nat) -> m + n == n + m
plusComm :: Nf
plusComm = prod [("m", NfNat), ("n", NfNat)] $
  NfId NfNat (plusTm @@ var "m" @@ var "n") (plusTm @@ var "n" @@ var "m")

-- (m n k : Nat) -> Eq (plus m (plus n k)) (plus (plus m n) k)
plusAssoc :: Nf
plusAssoc = prod [("m", NfNat), ("n", NfNat), ("k", NfNat)] $
  NfId NfNat
    (plusTm @@ var "m" @@ (plusTm @@ var "n" @@ var "k"))
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
    lam [("m", NfNat), ("n", NfNat)] $
    NfSuc (NfSuc (var "n"))

-- (A -> B) -> ~B -> ~A
contrapos :: Nf
contrapos = prod [("A", type0), ("B", type0)] $
  (var "A" ==> var "B") ==> neg (var "B") ==> neg (var "A")

-- (B -> C) -> (A -> B) -> A -> C
compose :: Nf
compose = prod [("A", type0), ("B", type0), ("C", type0)] $
  (var "B" ==> var "C") ==> (var "A" ==> var "B") ==> var "A" ==> var "C"

{-
(A : Type) (B : A -> Type) (C : (x : A) -> B cx -> Type) ->
((x : A) (y : B x) -> C x y) ->
(f : (x : A) -> B x) ->
(x : A) -> C x (f x)
-}
depCompose :: Nf
depCompose =
  prod [
  ("A", type0),
  ("B", var "A" ==> type0),
  ("C", NfPi "x" (var "A") $ var "B" @@ var "x" ==> type0)] $
  (NfPi "x" (var "A") $ NfPi "y" (var "B" @@ var "x") $ var "C" @@ var "x" @@ var "y") ==>
  NfPi "g" (NfPi "x" (var "A") $ var "B" @@ var "x")
  (NfPi "x" (var "A") $ var "C" @@ var "x" @@ (var "g" @@ var "x"))

-- (A * B -> C) -> A -> B -> C
curryTy :: Nf
curryTy = prod [("A", type0), ("B", type0), ("C", type0)] $
  (var "A" ** var "B" ==> var "C") ==> var "A" ==> var "B" ==> var "C"

-- (A -> B -> C) -> A * B -> C
uncurryTy :: Nf
uncurryTy = prod [("A", type0), ("B", type0), ("C", type0)] $
  (var "A" ==> var "B" ==> var "C") ==> var "A" ** var "B" ==> var "C"

natIsDiscrete :: Nf
natIsDiscrete = isDiscrete NfNat

-- isEven n = [k : Nat] (2 * k == n)
isEven :: Nf -> Nf
isEven n = NfSigma "k" NfNat $ NfId NfNat (doubleTm @@ var "k") n

-- isOdd n = ~ isEven n
isOdd :: Nf -> Nf
isOdd n = neg (isEven n)


-- isEvenPlusTwo = (n : Nat) -> isEven n -> isEven (suc (suc n))
isEvenPlusTwo :: Nf
isEvenPlusTwo =
  NfPi "n" NfNat $
  isEven (var "n") ==> isEven (NfSuc $ NfSuc $ var "n")

numeral :: Int -> Nf
numeral 0 = NfZero
numeral i = NfSuc (numeral (i-1))

-- f m n == 2 * m + 2 * n
polySpec :: Nf
polySpec =
  NfSigma "f" (NfNat ==> NfNat ==> NfNat) $
  NfPi "m" NfNat $ NfPi "n" NfNat $
  NfId NfNat (var "f" @@ var "m" @@ var "n") (plusTm @@ (doubleTm @@ var "m") @@ (doubleTm @@ var "n"))

{-
(<=) : Nat -> Nat -> Type
zero  <= n     = Unit
suc m <= zero  = Empty
suc m <= suc n = m <= n

Leq = NatRec (\n.Unit) (\m f.NatRec Empty (\n g.f n)
-}
leqNat :: Nf
leqNat =
  natRec (NfNat ==> type0)
    (NfLam "n" NfNat $ NfUnit)
    (NfLam "m" NfNat $ NfLam "f" (NfNat ==> type0) $
      natRec type0 NfEmpty $
        NfLam "n" NfNat $ NfLam "g" type0 $ var "f" @@ var "n")

{-
max m n <= m
max m n <= n
max m n == m + max m n == n
-}
maxSpec :: Nf
maxSpec =
  NfSigma "f" (NfNat ==> NfNat ==> NfNat) $
    (NfPi "m" NfNat $ NfPi "n" NfNat $ leqNat @@ (var "f" @@ var "m" @@ var "n") @@ var "m") **
    (NfPi "m" NfNat $ NfPi "n" NfNat $ leqNat @@ (var "f" @@ var "m" @@ var "n") @@ var "n") **
    (NfPi "m" NfNat $ NfPi "n" NfNat $
      NfId NfNat (var "f" @@ var "m" @@ var "n") (var "m") ||
      NfId NfNat (var "f" @@ var "m" @@ var "n") (var "n"))

{-
plus 0       n == n
plus (suc m) n == suc (plus m n)
-}
plusSpec :: Nf
plusSpec =
  NfSigma "f" (NfNat ==> NfNat ==> NfNat) $
    (NfPi "n" NfNat $ NfId NfNat (var "f" @@ NfZero @@ var "n") (var "n")) **
    (prod [("m",NfNat), ("n",NfNat)] $
      NfId NfNat (var "f" @@ NfSuc (var "m") @@ var "n") (NfSuc (var "f" @@ var "m" @@ var "n")))

isMonoid :: Nf -> Nf
isMonoid a =
  sig [("u", a), ("f", a ==> a ==> a)] $
    (NfPi "x" a $ NfId a (var "f" @@ var "u" @@ var "x") (var "x")) **
    (NfPi "x" a $ NfId a (var "f" @@ var "x" @@ var "u") (var "x")) **
    (prod [("x", a), ("y", a), ("z", a)] $
      NfId a
        (var "f" @@ (var "f" @@ var "x" @@ var "y") @@ var "z")
        (var "f" @@ var "x" @@ (var "f" @@ var "y" @@ var "z")))

maxExamples :: [(Int, Int, Int)]
maxExamples =
  [(0,0,0), (0,1,1), (1,0,1), (1,1,1), (2,1,2),
   (1,2,2), (2,2,2), (2,3,3)]

ioSpec :: Nf -> Nf -> [(Nf, Nf, Nf)] -> Nf
ioSpec f b [] = NfUnit
ioSpec f b ((x,y,z):[]) = NfId b (f @@ x @@ y) z
ioSpec f b ((x,y,z):(x',y',z'):vs) = 
  NfId b (f @@ x @@ y) z **
  ioSpec f b ((x',y',z'):vs)

maxIOSpec :: Nf
maxIOSpec =
  NfSigma "f" (NfNat ==> NfNat ==> NfNat) $
  ioSpec (var "f") NfNat [(numeral i, numeral j, numeral k) | (i, j, k) <- maxExamples]

leftId :: Nf -> Nf -> Nf -> Nf
leftId a f e = NfPi "x" a $ NfId a (f @@ e @@ var "x") (var "x")

rightId :: Nf -> Nf -> Nf -> Nf
rightId a f e = NfPi "x" a $ NfId a (f @@ var "x" @@ e) (var "x")

associative :: Nf -> Nf -> Nf
associative a f =
  prod [("x",a),("y",a),("z",a)] $
  NfId a (f @@ var "x" @@ (f @@ var "y" @@ var "z"))
         (f @@ (f @@ var "x" @@ var "y") @@ var "z")

identityUnique :: Nf
identityUnique =
  prod [("A", type0), ("f", var "A" ==> var "A" ==> var "A"),
        ("e1", var "A"), ("e2", var "A")] $
    leftId (var "A") (var "f") (var "e1") ==>
    rightId (var "A") (var "f") (var "e1") ==>
    leftId (var "A") (var "f") (var "e2") ==>
    rightId (var "A") (var "f") (var "e2") ==>
    NfId (var "A") (var "e1") (var "e2")

inverseUnique :: Nf
inverseUnique =
  prod [("A", type0), ("f", var "A" ==> var "A" ==> var "A"),
        ("e", var "A"), ("a", var "A"), ("b", var "A"), ("c", var "A")] $
    associative (var "A") (var "f") ==>
    leftId (var "A") (var "f") (var "e") ==>
    rightId (var "A") (var "f") (var "e") ==>
    NfId (var "A") (var "f" @@ var "a" @@ var "b") (var "e") ==> 
    NfId (var "A") (var "f" @@ var "b" @@ var "a") (var "e") ==> 
    NfId (var "A") (var "f" @@ var "a" @@ var "c") (var "e") ==> 
    NfId (var "A") (var "f" @@ var "c" @@ var "a") (var "e") ==> 
    NfId (var "A") (var "b") (var "c")

types :: [Nf]
types =
  [notInvolTy, plusZero, plusAssoc, plusComm, isEven (numeral 20),
  isEvenPlusTwo, plusSpec, isMonoid NfNat,
  identityUnique, inverseUnique]

ctx :: Ctx
ctx = empty

doSynth :: Nf -> IO Nf
doSynth t = do
  putStrLn $ showCtx ctx ++ " ⊢ ? : " ++ show t
  t <- timeIt (return $ head $ synthAll ctx t)
  putStrLn ""
  return t

main :: IO ()
main = do
  mapM_ doSynth $ types
  return ()