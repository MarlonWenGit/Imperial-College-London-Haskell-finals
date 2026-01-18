module Solver where

import Data.List 
import Data.Char
import qualified Data.Set as S

import Types
import WordData
import Clues
import Examples

import Control.Monad (guard)

------------------------------------------------------
-- Part I

punctuation :: String
punctuation 
  = "';.,-!?"

cleanUp :: String -> String
cleanUp
  = map toLower . filter (`notElem` punctuation)

split2 :: [a] -> [([a], [a])]
split2 xs
  = [splitAt i xs | i <- [1..(length xs - 1)]]
    where l = length xs

split3 :: [a] -> [([a], [a], [a])]
split3 xs
  = do 
    (xs1, xs2) <- split2 xs
    (xs1, [], xs2) : [(xs1, xs2', xs2'') | (xs2', xs2'') <- split2 xs2]
    
uninsert :: [a] -> [([a], [a])]
uninsert xs
  = do
    (xs1, xs2, xs3) <- split3 xs
    if not (null xs2)
      then return (xs2, xs1 ++ xs3)
      else []

split2M :: [a] -> [([a], [a])]
split2M xs
  = sxs ++ [(y, x) | (x, y) <- sxs] 
  where
    sxs = split2 xs

split3M :: [a] -> [([a], [a], [a])]
split3M xs
  = sxs ++ [(z, y, x) | (x, y, z) <- sxs]
  where
    sxs = split3 xs

------------------------------------------------------
-- Part II

matches :: String -> ParseTree -> Bool
matches s (Synonym s2)
  = s `elem` (synonyms s2)

matches s (Anagram _ s2)
  = (sort s) == (sort s2)

matches s (Reversal _ t)
  = matches (reverse s) t

matches s (Insertion _ lt rt)
  = any (\(xs1, xs2) -> 
    ((matches xs1 lt) && (matches xs2 rt)) || ((matches xs2 lt) && (matches xs1 rt))
  ) 
  (uninsert s)

matches s (Charade _ lt rt)
  = any (\(xs1, xs2) -> 
    ((matches xs1 lt) && (matches xs2 rt)) || ((matches xs2 lt) && (matches xs1 rt))
  ) 
  (split2 s)

evaluate :: Parse -> Int -> [String]
evaluate (d, _, t) n = 
  filter (\s -> matches s t) $
  filter (\s -> length s == n) $
  synonyms (unwords d)

------------------------------------------------------
-- Part III

-- Given...
parseWordplay :: [String] -> [ParseTree]
parseWordplay ws
  = concat [parseSynonym ws,
            parseAnagram ws,
            parseReversal ws,
            parseInsertion ws,
            parseCharade ws]
    
parseSynonym :: [String] -> [ParseTree]
parseSynonym xs
  = if null (synonyms s)
    then []
    else [Synonym s]
    where s = unwords xs

parseAnagram :: [String] -> [ParseTree]
parseAnagram xs
  = do 
    (xs1, xs2) <- split2M xs
    if (elem (unwords xs1) anagramIndicators)
      then [Anagram xs1 (concat xs2)]
      else []
    
parseReversal :: [String] -> [ParseTree]
parseReversal xs
  = do 
    (xs1, xs2) <- split2M xs
    if (elem (unwords xs1) reversalIndicators)
      then [Reversal xs1 t | t <- parseWordplay xs2]
      else []

parseInsertion :: [String] -> [ParseTree]
parseInsertion xs
  = do 
    (arg, ws, arg') <- split3 xs
    let ind = unwords ws
    (inner, outer) <- [(arg, arg') | ind `elem` insertionIndicators] ++ 
                      [(arg', arg) | ind `elem` envelopeIndicators]
    x <- parseWordplay inner
    x' <- parseWordplay outer
    return (Insertion ws x x')

parseCharade :: [String] -> [ParseTree]
parseCharade xs
  = do 
    (arg, ws, arg') <- split3 xs
    let ind = unwords ws
    (inner, outer) <- [(arg, arg') | ind `elem` beforeIndicators] ++ 
                      [(arg', arg) | ind `elem` afterIndicators]
    x <- parseWordplay inner
    x' <- parseWordplay outer
    return (Charade ws x x')

-- Given...
parseClue :: Clue -> [Parse]
parseClue clue@(s, n)
  = parseClueText (words (cleanUp s))

parseClueText :: [String] -> [Parse]
parseClueText xs
  = do
    (d, l, w) <- split3M xs
    guard (elem (unwords l) linkWords)
    guard ((length $ synonyms $ unwords d) >= 1)
    t <- parseWordplay w
    return (d, l, t)

solve :: Clue -> [Solution]
solve clue@(s, n)
  = do
    p <- parseClue clue
    let s = (evaluate p n)
    guard (not $ null s)
    return (clue, p, unwords s)

------------------------------------------------------
-- Some additional test functions

-- Returns the solution(s) to the first k clues.
-- The nub removes duplicate solutions arising from the
-- charade parsing rule.
solveAll :: Int -> [[String]]
solveAll k
  = map (nub . map getSol . solve . (clues !!)) [0..k-1]

getSol :: Solution -> String
getSol (_, _, sol) = sol

showAll
  = mapM_ (showSolutions . solve . (clues !!)) [0..23]


