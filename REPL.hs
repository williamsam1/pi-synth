{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses, AllowAmbiguousTypes #-}

import System.IO
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
import Parser
import Synthesis

data Command
  = Define String Term
  | DefineCheck String Term Term
  | Synthesize String Term
  deriving (Eq,Show)

cmd :: Grammar r (Prod r String String Command)
cmd = mdo
  e        <- expr
  defTm    <- rule $ Define <$> ident <* defEq <*> (desugar <$> e)
  defChkTm <- rule $ DefineCheck <$> ident <* doublecolon <*> (desugar <$> e) <* defEq <*> (desugar <$> e)
  synthTy  <- rule $ Synthesize <$> ident <* questioncolon <*> (desugar <$> e)
  cmd      <- rule $ defTm <|> defChkTm <|> synthTy
  return cmd

data REPLError
  = ParseErr Int (Report String [String])
  | TypeErr Int TypeCheckError
  | EnvErr Int String

instance Show REPLError where
  show (ParseErr i err) = "Parse error on line " ++ show i ++ "\n" ++ show err
  show (TypeErr i err)  = "Type-check error on line " ++ show i ++ "\n" ++ show err
  show (EnvErr i x)     = "On line " ++ show i ++ "\n" ++ show x ++ " is already defined"

type State = (Env, Ctx)

emp :: State
emp = (Map.empty, Map.empty)

parseCmd :: Int -> String -> Either REPLError Command
parseCmd i xs =
  let (cs, r) = fullParses (parser cmd) $ tokenize xs in
  case cs of
    []     -> Left (ParseErr i r)
    (c:cs) -> Right c

runRepl :: Int -> State -> Command -> Either REPLError State
runRepl i (env, ctx) (Define x t) =
  if x `Map.member` env then Left (EnvErr i x) else
  case infer env ctx t of
    Left err -> Left (TypeErr i err)
    Right v  -> Right (Map.insert x v env, ctx)
runRepl i (env, ctx) (DefineCheck x a t) =
  if x `Map.member` env then Left (EnvErr i x) else
  case check env ctx a (NfS (Type 0)) of
    Left err -> case check env ctx a (NfS (Type 1)) of
      Left err -> Left (TypeErr i err)
      Right a -> case check env ctx t a of
        Left err -> Left (TypeErr i err)
        Right t  -> Right (Map.insert x (t, a) env, ctx)
    Right a  -> case check env ctx t a of
      Left err -> Left (TypeErr i err)
      Right t  -> Right (Map.insert x (t, a) env, ctx)
runRepl i (env, ctx) (Synthesize x a) =
  if x `Map.member` env then Left (EnvErr i x) else
  case check env ctx a (NfS (Type 0)) of
    Left err -> case check env ctx a (NfS (Type 1)) of
      Left err -> Left (TypeErr i err)
      Right a -> let t = head (synthAll ctx a) in
        Right (Map.insert x (t, a) env, ctx)
    Right a  -> let t = head (synthAll ctx a) in
      Right (Map.insert x (t, a) env, ctx)

repl :: Int -> [String] -> State -> Either REPLError State
repl i []     s = Right s
repl i (x:xs) s =
  if all isSpace x then repl (i+1) xs s else
  do
  c <- parseCmd i x
  s <- runRepl i s c
  repl (i+1) xs s

runFile :: String -> Either REPLError State
runFile contents = repl 0 (lines contents) emp

main :: IO ()
main = do
  xs:_ <- getArgs
  handle <- openFile xs ReadMode
  contents <- hGetContents handle  
  print (runFile contents)
  hClose handle

-- main :: IO ()
-- main = do
--   xs:_ <- getArgs
--   print $ tokenize xs
--   (ps, r) <- return $ fullParses (parser expr) $ tokenize xs
--   mapM_ print ps
--   putStrLn ""
--   print $ parseTerm xs
--   putStrLn ""
--   print $ desugar <$> parseTerm xs
--   putStrLn ""
--   print $ infer Map.empty Map.empty <$> desugar <$> parseTerm xs
--   putStrLn ""
--   print $ check Map.empty Map.empty <$> (desugar <$> parseTerm xs) <*> (pure $ NfS (Type 0))
--   putStrLn ""
--   print $ check Map.empty Map.empty <$> (desugar <$> parseTerm xs) <*> (pure $ NfS (Type 1))
