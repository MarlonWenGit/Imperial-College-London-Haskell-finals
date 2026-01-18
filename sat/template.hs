module SOL where

import Data.List
import Data.Maybe

import Types
import TestData

printF :: Formula -> IO()
printF
  = putStrLn . showF
  where
    showF (Var v)
      = v
    showF (Not f)
      = '!' : showF f
    showF (And f f')
      = "(" ++ showF f ++ " & " ++ showF f' ++ ")"
    showF (Or f f')
      = "(" ++ showF f ++ " | " ++ showF f' ++ ")"

--------------------------------------------------------------------------
-- Part I

-- 1 mark
lookUp :: Eq a => a -> [(a, b)] -> b
-- Pre: The item being looked up has a unique binding in the list
lookUp k xs = fromJust $ lookup k xs

-- 3 marks
vars :: Formula -> [Id]
vars = nub . sort . vars'
  where
    vars' :: Formula -> [Id]
    vars' (Var id)    = [id]
    vars' (Not f)     = vars' f
    vars' (And f1 f2) = (vars' f1) ++ (vars' f2)
    vars' (Or f1 f2)  = (vars' f1) ++ (vars' f2)

-- 1 mark
idMap :: Formula -> IdMap
idMap f = zip (vars f) [1..]

--------------------------------------------------------------------------
-- Part II

-- An encoding of the Or distribution rules.
-- Both arguments are assumed to be in CNF, so the
-- arguments of all And nodes will also be in CNF.
distribute :: CNF -> CNF -> CNF
distribute a (And b c)
  = And (distribute a b) (distribute a c)
distribute (And a b) c
  = And (distribute a c) (distribute b c)
distribute a b
  = Or a b

-- 4 marks
toNNF :: Formula -> NNF
toNNF (Not (Not f)) = toNNF f
toNNF (Not (And f1 f2)) = Or (toNNF (Not f1)) (toNNF (Not f2))
toNNF (Not (Or f1 f2)) = And (toNNF (Not f1)) (toNNF (Not f2))

toNNF (And f1 f2) = And (toNNF f1) (toNNF f2)
toNNF (Or f1 f2) = Or (toNNF f1) (toNNF f2)
toNNF (Not f) = Not (toNNF f)
toNNF var = var

-- 3 marks
toCNF :: Formula -> CNF
toCNF = toCNF' . toNNF
  where
    toCNF' :: NNF -> CNF
    toCNF' (Or a b) = distribute (toCNF' a) (toCNF' b)
    toCNF' (And a b) = And (toCNF' a) (toCNF' b)
    toCNF' f = f

-- 4 marks
flatten :: CNF -> CNFRep
flatten f = flatten' (idMap f) f
  where
    flatten' :: IdMap -> CNF -> CNFRep
    flatten' idM (Var id) = [[lookUp id idM]]
    flatten' idM (Not (Var id)) = [[negate $ lookUp id idM]]
    flatten' idM (And a b) = (flatten' idM a) ++ (flatten' idM b)
    flatten' idM (Or a b) 
      = [x ++ y | x <- (flatten' idM a), y <- (flatten' idM b)]

--------------------------------------------------------------------------
-- Part III

-- 5 marks
propUnits :: CNFRep -> (CNFRep, [Int])
propUnits xss 
  | null u = (xss, [])
  | otherwise = (xss', (fromJust u):us)
  where 
    u = findUnit xss
    (xss', us) = propUnits (deleteUnit (fromJust u) xss)

    findUnit :: CNFRep -> Maybe Int
    findUnit [] = Nothing
    findUnit ([x]:xss) = Just x
    findUnit (xs:xss) = findUnit xss

    deleteUnit :: Int -> CNFRep -> CNFRep
    deleteUnit _ [] = []
    deleteUnit l (xs:xss) 
      | elem l xs = deleteUnit l xss
      | otherwise = (filter (/= (negate l)) xs) : (deleteUnit l xss)

-- 4 marks
dp :: CNFRep -> [[Int]]
dp = dp' . propUnits
  where 
    dp' :: (CNFRep, [Int]) -> [[Int]]
    dp' ([], us) = [us]
    dp' (c, us) | elem [] c = []
    dp' (c@((x:_):_), us) 
      = [us ++ ys | ys <- ((dp ([x]:c)) ++ (dp ([negate x]:c)))]

--------------------------------------------------------------------------
-- Part IV

-- Bonus 2 marks
allSat :: Formula -> [[(Id, Bool)]]
allSat f
  = map (assignBool (idMap f)) (dp . flatten $ toCNF f)

assignBool :: IdMap -> [Int] -> [(Id, Bool)]
assignBool _ [] = []
assignBool idM (x:xs) = (lookUp x idM, x < 0) : (assignBool xs)
