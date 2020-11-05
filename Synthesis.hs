module Synthesis where

import Data.Map (Map, empty, insert, lookup, toList)
import qualified Data.Map as Map
import qualified Data.Set as Set

import Core

synthAll :: Ctx -> Nf -> [Nf]
synthAll ctx a = concat [synth s ctx a | s <- [0..]]

synthUpto :: Int -> Ctx -> Nf -> [Nf]
synthUpto m ctx a = concat [synth s ctx a | s <- [0..m]]

synth :: Int -> Ctx -> Nf -> [Nf]
synth s ctx a = 
  if s < 0
    then []
    else
      synthCtx s ctx a ++ synthTy s ctx a

synthSpinesHelper :: Int -> Ctx -> [(Ne, Nf, Int)] -> [(Ne, Nf)]
synthSpinesHelper s ctx [] = []
synthSpinesHelper s ctx ((n, NfPi x a b, s1):xs) =
  if s1 >= s
    then (n, NfPi x a b) : synthSpinesHelper s ctx xs
    else synthSpinesHelper s ctx (ys ++ xs)
  where
    ys :: [(Ne, Nf, Int)]
    ys = [(NeApp n v, substNf x v b, s1+s2) | s2 <- [0..s-s1-1], v <- synth s2 ctx a]
synthSpinesHelper s ctx ((n, NfSigma x a b, s1):xs) =
  if s1 >= s
    then (n, NfSigma x a b) : synthSpinesHelper s ctx xs
    else synthSpinesHelper s ctx (ys ++ xs)
  where
    ys :: [(Ne, Nf, Int)]
    ys = [(NeFst n, a, 1+s1), (NeSnd n, substNf x (NfNe (NeFst n)) b, 1+s1)]
synthSpinesHelper s ctx ((n, t, s1):xs) = 
  (n, t) : synthSpinesHelper s ctx xs

-- Generate all valid spines from the context
-- Not very efficient, but general
-- Is it possible to try and unify variable codomains
-- with goal types for a more efficient procedure?
synthSpines :: Int -> Ctx -> [(Ne, Nf)]
synthSpines s ctx = synthSpinesHelper s ctx [(NeV x, t, 0) | (x, t) <- toList ctx]

-- Context-guided search (spines)
synthCtx :: Int -> Ctx -> Nf -> [Nf]
synthCtx s ctx a = [NfNe n | (n, t) <- synthSpines s ctx, t == a]

-- Type-guided search (introduction forms)
synthTy :: Int -> Ctx -> Nf -> [Nf]
synthTy s ctx (NfS i)         = synthSort s ctx i
synthTy s ctx (NfPi x a b)    = synthProd s ctx x a b
synthTy s ctx NfUnit          = if s == 0 then [NfTT] else []
synthTy s ctx NfNat           = synthNat s ctx
synthTy s ctx (NfSum a b)     = synthSum s ctx a b
synthTy s ctx (NfSigma x a b) = synthPair s ctx x a b
synthTy s ctx _               = []

synthNat :: Int -> Ctx -> [Nf]
synthNat 0 ctx = [NfZero]
synthNat s ctx = [NfSuc n | n <- synth (s-1) ctx NfNat]

synthSum :: Int -> Ctx -> Nf -> Nf -> [Nf]
synthSum 0 ctx a b = []
synthSum s ctx a b =
  [NfInl t b | t <- synth (s-1) ctx a] ++
  [NfInr t a | t <- synth (s-1) ctx b]

synthPair :: Int -> Ctx -> String -> Nf -> Nf -> [Nf]
synthPair 0 ctx x a b = []
synthPair s ctx x a b =
  [NfPair t v | s1 <- [0..s-1], t <- synth s1 ctx a, v <- synth (s-1-s1) ctx (substNf x t b)]

synthSort :: Int -> Ctx -> Sort -> [Nf]
synthSort s ctx (Type i) =
  if s == 0 && i > 0
    then [NfS (Type (i - 1))]
    else tjti ++ titj
  where
    x :: String
    x = newName "A" (Map.keysSet ctx)
    tjti :: [Nf]
    tjti = [NfPi x a b | s1 <- [0..s-1], j <- [0..i], a <- synth s1 ctx (NfS (Type j)), b <- synth (s-1-s1) (insert x a ctx) (NfS (Type i))]
    titj :: [Nf]
    titj = [NfPi x a b | s1 <- [0..s-1], j <- [0..i], a <- synth s1 ctx (NfS (Type i)), b <- synth (s-1-s1) (insert x a ctx) (NfS (Type j))]

synthProd :: Int -> Ctx -> String -> Nf -> Nf -> [Nf]
synthProd s ctx x a b = synthLam s ctx x a b ++ synthRec s ctx x a b

-- Synthesize product as a lambda abstraction
synthLam :: Int -> Ctx -> String -> Nf -> Nf -> [Nf]
synthLam s ctx x a b = [NfLam y a t | t <- synth (s-1) (insert y a ctx) b]
  where
    -- We need a new unused variable for the lambda
    -- abstraction if this is an arrow type
    y :: String
    y = if x == "_"
      then newName (niceVar a) (Map.keysSet ctx `Set.union` boundVarsNf b)
      else x

-- Synthesize product with an induction principle
synthRec :: Int -> Ctx -> String -> Nf -> Nf -> [Nf]
synthRec s ctx x NfEmpty p = if s == 0 then [NfEmptyInd (NfLam x NfUnit p)] else []
synthRec s ctx x NfUnit p = 
  [ NfUnitInd (NfLam x NfUnit p) t |
    t <- synth (s-1) ctx (substNf x NfTT p) ]
synthRec s ctx x (NfSum a b) p = 
  [ NfSumInd (NfLam x (NfSum a b) p) f g |
    s1 <- [0..s-1],
    f <- synth s1 ctx (NfPi y a $ substNf x (NfInl (var y) b) p),
    g <- synth (s-1-s1) ctx (NfPi z b $ substNf x (NfInr (var z) a) p) ]
  where
    y :: String
    y = newName (niceVar a)
          (Map.keysSet ctx `Set.union`
          boundVarsNf p `Set.union`
          Set.singleton x)
    z :: String
    z = newName (niceVar b)
          (Map.keysSet ctx `Set.union`
          boundVarsNf p `Set.union`
          Set.singleton x)
synthRec s ctx x (NfSigma y a b) p = 
  [ NfProdInd (NfLam x (NfSigma y a b) p) f |
    f <- synth (s-1) ctx (NfPi y a $ NfPi z b $ substNf x (NfPair (var y) (var z)) p) ]
  where
    z :: String
    z = newName (niceVar b)
          (Map.keysSet ctx `Set.union`
          boundVarsNf p `Set.union`
          Set.singleton x `Set.union`
          Set.singleton y)
synthRec s ctx x NfNat p = 
  [ NfNatInd (NfLam x NfNat p) z s |
    s1 <- [0..s-1],
    z <- synth s1 ctx (substNf x NfZero p),
    s <- synth (s-1-s1) ctx sType ]
  where
    sType :: Nf
    sType =
      NfPi y NfNat $ substNf x (var y) p ==> substNf x (NfSuc (var y)) p
    y :: String
    y = newName "n" (Map.keysSet ctx `Set.union` boundVarsNf p `Set.union` Set.singleton x)
synthRec _ _ _ _ _ = []