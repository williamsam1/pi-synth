module Synthesis where

import Data.Maybe (catMaybes)
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
      synthNe s ctx a ++ synthTy s ctx a

synthNeHelper :: Int -> Ctx -> [(Ne, Nf, Int)] -> [(Ne, Nf)]
synthNeHelper s ctx [] = []
synthNeHelper s ctx ((n, NfPi x a b, s1):xs) =
  if s1 >= s
    then (n, NfPi x a b) : synthNeHelper s ctx xs
    else synthNeHelper s ctx (ys ++ xs)
  where
    ys :: [(Ne, Nf, Int)]
    ys = [(NeApp n v, substNf x v b, s1+s2) | s2 <- [0..s-s1-1], v <- synth s2 ctx a]
synthNeHelper s ctx ((n, NfSigma x a b, s1):xs) =
  if s1 >= s
    then (n, NfSigma x a b) : synthNeHelper s ctx xs
    else synthNeHelper s ctx (ys ++ xs)
  where
    ys :: [(Ne, Nf, Int)]
    ys = [(NeFst n, a, 1+s1), (NeSnd n, substNf x (NfNe (NeFst n)) b, 1+s1)]
synthNeHelper s ctx ((n, t, s1):xs) = 
  (n, t) : synthNeHelper s ctx xs

-- Generate all neutral forms in the given context
-- Not very efficient, but general
-- Is it possible to try and unify variable codomains
-- with goal types for a more efficient procedure?
-- May consider doing this only for large context sizes
synthAllNe :: Int -> Ctx -> [(Ne, Nf)]
synthAllNe s ctx = synthNeHelper s ctx [(NeV x, t, 0) | (x, t) <- toList ctx]

-- Context-guided search (neutral forms)
synthNe :: Int -> Ctx -> Nf -> [Nf]
synthNe s ctx a = [NfNe n | (n, t) <- synthAllNe s ctx, t == a]

-- Type-guided search (introduction forms)
synthTy :: Int -> Ctx -> Nf -> [Nf]
synthTy s ctx (NfS i)         = synthSort s ctx i
synthTy s ctx (NfPi x a b)    = synthProd s ctx x a b
synthTy s ctx NfUnit          = if s == 0 then [NfTT] else []
synthTy s ctx NfNat           = synthNat s ctx
synthTy s ctx (NfSum a b)     = synthSum s ctx a b
synthTy s ctx (NfSigma x a b) = synthPair s ctx x a b
synthTy s ctx (NfId a x y)    = synthPath s ctx a x y
synthTy s ctx (NfW a b)       = synthInd s ctx a b
synthTy s ctx _               = []

synthNat :: Int -> Ctx -> [Nf]
synthNat 0 ctx = [NfZero]
synthNat s ctx = [NfSuc n | n <- synth (s-1) ctx NfNat]

synthSum :: Int -> Ctx -> Nf -> Nf -> [Nf]
synthSum 0 ctx a b = []
synthSum s ctx a b =
  [NfInl t b | t <- synth (s-1) ctx a] ++
  [NfInr t a | t <- synth (s-1) ctx b]

synthInd :: Int -> Ctx -> Nf -> Nf -> [Nf]
synthInd 0 ctx a b = []
synthInd s ctx a b =
  [ NfSup a b x u |
    s1 <- [0..s-1],
    x <- synth s1 ctx a,
    u <- synth (s-s1-1) ctx (b @@ x ==> NfW a b) ]

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
    x = freeNameCtx "A" ctx
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
    sType = NfPi y NfNat $ substNf x (var y) p ==> substNf x (NfSuc (var y)) p
    y = newName "n" (Map.keysSet ctx `Set.union` boundVarsNf p `Set.union` Set.singleton x)
synthRec s ctx w (NfW a b) p = 
  [ NfWInd a b (NfLam w (NfW a b) p) f | f <- synth (s-1) ctx fType ]
  where
    -- (x : A) (u : B x -> W A B) -> ((b : B x) -> P (u b)) -> P (sup x u)
    fType =
      NfPi xV a $
      NfPi uV (b @@ var xV ==> NfW a b) $
      (NfPi bV (b @@ var xV) $ substNf w (var uV @@ var bV) p) ==>
      substNf w (NfSup a b (var xV) (var uV)) p
    xV = newName "x" (Map.keysSet ctx `Set.union` boundVarsNf p `Set.union` Set.singleton w)
    uV = newName "u" (Map.keysSet ctx `Set.union` boundVarsNf p `Set.union` Set.singleton w)
    bV = newName "b" (Map.keysSet ctx `Set.union` boundVarsNf p `Set.union` Set.singleton w)
synthRec _ _ _ _ _ = []


-- Finds all paths which are in neutral form
synthAllNePaths :: Int -> Ctx -> [(Nf, Nf, Nf)]
synthAllNePaths s ctx = catMaybes [f n t | (n, t) <- synthAllNe s ctx]
  where
    f :: Ne -> Nf -> Maybe (Nf, Nf, Nf)
    f n (NfId _ a b) = Just (NfNe n, a, b)
    f _ _ = Nothing

{-
Helper for finding paths using congruence

if
  subtermNf s t == Just Nothing
then
  s == t

if
  subtermNf s t == Just (Just f)
then
  f @@ s == t
-}
subtermNf :: Ctx -> Nf -> Nf -> Maybe (Maybe Nf)
subtermNf ctx x y | x == y = Just Nothing
subtermNf ctx (NfNe x) (NfNe y) = subtermNe ctx x y
subtermNf ctx x (NfSuc y) = case subtermNf ctx x y of
  Nothing       -> Nothing
  Just Nothing  -> Just $ Just $ NfLam v NfNat $ NfSuc (var v)
  Just (Just f) -> Just $ Just $ NfLam v NfNat $ NfSuc (f @@ var v)
  where
    v :: String
    v = freeNameCtx "n" ctx
subtermNf ctx x (NfInl y a) = case subtermNf ctx x y of
  Nothing       -> Nothing
  Just Nothing  -> Just $ Just $ NfLam v NfNat $ NfInl (var v) a
  Just (Just f) -> Just $ Just $ NfLam v NfNat $ NfInl (f @@ var v) a
  where
    v :: String
    v = freeNameCtx (niceVar a) ctx
subtermNf ctx x (NfInr y b) = case subtermNf ctx x y of
  Nothing       -> Nothing
  Just Nothing  -> Just $ Just $ NfLam v NfNat $ NfInr (var v) b
  Just (Just f) -> Just $ Just $ NfLam v NfNat $ NfInr (f @@ var v) b
  where
    v :: String
    v = freeNameCtx (niceVar b) ctx
subtermNf ctx x y = Nothing

subtermNe :: Ctx -> Ne -> Ne -> Maybe (Maybe Nf)
subtermNe ctx x y | x == y = Just Nothing
subtermNe ctx x (NeFst y) = case subtermNe ctx x y of
  Nothing       -> Nothing
  Just Nothing  -> Just $ Just $ NfLam v t $ NfNe (NeFst (NeV v))
  Just (Just f) -> Just $ Just $ NfLam v t $ NfFst z a b @@ (f @@ var v)
  where
    t :: Nf
    t = case getTypeNe ctx y of
      Right t -> t
    z :: String
    z = case t of
      NfSigma z _ _ -> z
    a :: Nf
    a = case t of
      NfSigma _ a _ -> a
    b :: Nf
    b = case t of
      NfSigma _ _ b -> b
    v :: String
    v = freeNameCtx (niceVar t) ctx
subtermNe ctx x (NeSnd y) = case subtermNe ctx x y of
  Nothing       -> Nothing
  Just Nothing  -> Just $ Just $ NfLam v t $ NfNe (NeSnd (NeV v))
  Just (Just f) -> Just $ Just $ NfLam v t $ NfSnd z a b @@ (f @@ var v)
  where
    t :: Nf
    t = case getTypeNe ctx y of
      Right t -> t
    z :: String
    z = case t of
      NfSigma z _ _ -> z
    a :: Nf
    a = case t of
      NfSigma _ a _ -> a
    b :: Nf
    b = case t of
      NfSigma _ _ b -> b
    v :: String
    v = freeNameCtx (niceVar t) ctx
subtermNe ctx x (NeEmptyInd p y) =
  case subtermNe ctx x y of
  Nothing       -> Nothing
  Just Nothing  -> Just $ Just $ NfLam v NfEmpty $ NfNe (NeEmptyInd p (NeV v))
  Just (Just f) -> Just $ Just $ NfLam v NfEmpty $ NfEmptyInd p @@ (f @@ var v)
  where
    v :: String
    v = freeNameCtx (niceVar NfEmpty) ctx
subtermNe ctx x (NeUnitInd p t y) =
  case subtermNe ctx x y of
  Nothing       -> Nothing
  Just Nothing  -> Just $ Just $ NfLam v NfUnit $ NfNe (NeUnitInd p t (NeV v))
  Just (Just f) -> Just $ Just $ NfLam v NfUnit $ NfUnitInd p t @@ (f @@ var v)
  where
    v :: String
    v = freeNameCtx (niceVar NfUnit) ctx
subtermNe ctx x (NeSumInd p s t y) =
  case subtermNe ctx x y of
  Nothing       -> Nothing
  Just Nothing  -> Just $ Just $ NfLam v st $ NfNe (NeSumInd p s t (NeV v))
  Just (Just f) -> Just $ Just $ NfLam v st $ NfSumInd p s t @@ (f @@ var v)
  where
    st :: Nf
    st = case getTypeNe ctx y of
      Right t -> t
    v :: String
    v = freeNameCtx (niceVar st) ctx
subtermNe ctx x (NeProdInd p s y) =
  case subtermNe ctx x y of
  Nothing       -> Nothing
  Just Nothing  -> Just $ Just $ NfLam v pr $ NfNe (NeProdInd p s (NeV v))
  Just (Just f) -> Just $ Just $ NfLam v pr $ NfProdInd p s @@ (f @@ var v)
  where
    pr :: Nf
    pr = case getTypeNe ctx y of
      Right t -> t
    v :: String
    v = freeNameCtx (niceVar pr) ctx
subtermNe ctx x (NeNatInd p s t y) =
  case subtermNe ctx x y of
  Nothing       -> Nothing
  Just Nothing  -> Just $ Just $ NfLam v st $ NfNe (NeNatInd p s t (NeV v))
  Just (Just f) -> Just $ Just $ NfLam v st $ NfNatInd p s t @@ (f @@ var v)
  where
    st :: Nf
    st = case getTypeNe ctx y of
      Right t -> t
    v :: String
    v = freeNameCtx (niceVar st) ctx
subtermNe ctx x (NeApp n t) = case subtermNe ctx x n of
  Nothing -> case subtermNeNf ctx x t of
    Nothing       -> Nothing
    Just Nothing  -> Just $ Just $ NfLam tVar tTy $ NfNe n @@ var tVar
    Just (Just f) -> Just $ Just $ NfLam tVar tTy $ NfNe n @@ (f @@ var tVar)
  Just Nothing  -> Just $ Just $ NfLam nVar nTy $ var nVar @@ t
  Just (Just f) -> Just $ Just $ NfLam nVar nTy $ f @@ var nVar @@ t
  where
    nTy :: Nf
    nTy = case getTypeNe ctx n of
      Right a -> a
    nVar :: String
    nVar = freeNameCtx (niceVar nTy) ctx
    tTy :: Nf
    tTy = case getTypeNf ctx t of
      Right a -> a
    tVar :: String
    tVar = freeNameCtx (niceVar tTy) ctx
subtermNe ctx x y = Nothing

subtermNeNf :: Ctx -> Ne -> Nf -> Maybe (Maybe Nf)
subtermNeNf ctx x (NfNe y) = subtermNe ctx x y
subtermNeNf ctx x y        = Nothing

{-
  synthPathFrom0 c ctx x
finds all paths
  p : x == y
which are in neutral form,
or are congruence applied to a neutral form

p0 :== n | cong e n
-}
synthPathFrom0 :: Int -> Ctx -> Nf -> [(Nf, Nf)]
synthPathFrom0 s ctx x = catMaybes [f p a b | (p, a, b) <- synthAllNePaths s ctx]
    where
      f :: Nf -> Nf -> Nf -> Maybe (Nf, Nf)
      f p a b = case subtermNf ctx a x of
        Nothing       -> Nothing
        Just Nothing  -> Just (p, b)
        Just (Just f) -> Just (NfCong f p, f @@ b)

{-
  synthPathTo0 c ctx x
finds all paths
  p : y == x
which are in neutral form,
or are congruence applied to a neutral form

p0 :== n | cong e n
-}
synthPathTo0 :: Int -> Ctx -> Nf -> [(Nf, Nf)]
synthPathTo0 s ctx x = catMaybes [f p a b | (p, a, b) <- synthAllNePaths s ctx]
    where
      f :: Nf -> Nf -> Nf -> Maybe (Nf, Nf)
      f p a b = case subtermNf ctx b x of
        Nothing       -> Nothing
        Just Nothing  -> Just (p, a)
        Just (Just f) -> Just (NfCong f p, f @@ a)

{-
  synthPathFrom1 c ctx x
finds all paths
p : x == y
which are of the form p0,
or symmetry applied to p0

p1 :== p0 | Sym p0
-}
synthPathFrom1 :: Int -> Ctx -> Nf -> [(Nf, Nf)]
synthPathFrom1 s ctx x =
  synthPathFrom0 s ctx x ++
  [(NfSym p, y) | (p, y) <- synthPathTo0 s ctx x]

isInv :: Nf -> Nf -> Bool
isInv (NfSym p) q = p == q
isInv p (NfSym q) = p == q
isInv _ _ = False

{-
Don't want to include unnecessary refls
  p . refl == p
Also don't want to include redundant paths
  ~p . p . q == q
  p . ~p . q == q
-}
trans :: Nf -> Nf -> Maybe Nf
trans p (NfRefl _)    = Just p
trans p (NfTrans q r) =
  if isInv p q
    then Nothing
    else Just (NfTrans p (NfTrans q r))
trans p q             = Just (NfTrans p q)

{-
  synthPath2 c ctx x z
finds all paths
  p : x == z
which are of the form refl,
or transitivity applied to some
  p1 : x == y
  p2 : y == z

p2 :== Refl x | Trans p1 p2
-}
synthPath2 :: Int -> Ctx -> Nf -> Nf -> [Nf]
synthPath2 0 ctx x z =
  if x == z
    then [NfRefl x]
    else []
synthPath2 s ctx x z = catMaybes
  [ trans p q |
    s1 <- [0..s-1],
    (p, y) <- synthPathFrom1 s1 ctx x,
    q      <- synthPath2 (s-1-s1) ctx y z
  ]

{-
synthPath s ctx x y finds proofs that x == y
-}
synthPath :: Int -> Ctx -> Nf -> Nf -> Nf -> [Nf]
synthPath s ctx (NfPi x a b) f g =
  [ NfFunExt f g p |
    p <- synth (s-1) ctx (NfPi x a $ NfId b (f @@ var x) (g @@ var x)) ] ++
  synthPath2 s ctx f g
synthPath s ctx a x y = synthPath2 s ctx x y