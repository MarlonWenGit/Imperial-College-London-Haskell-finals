module Alloc where

import Data.Maybe
import Data.List
import Data.Ord
import qualified Data.Set as S

import Types
import Examples

------------------------------------------------------
--
-- Part I
--

count :: Eq a => a -> [a] -> Int
count x xs = length $ filter (==x) xs

degrees :: Eq a => Graph a -> [(a, Int)]
degrees ([], es) = []
degrees ((x:xs), es) 
  = (x, (count x ns1) + (count x ns2)) : degrees (xs, es)
    where (ns1, ns2) = unzip es

neighbours :: Eq a => a -> Graph a -> [a]
neighbours _ (_, []) = []
neighbours x (_, (n1, n2):es)
  | x == n1   = n2 : rest
  | x == n2   = n1 : rest
  | otherwise = rest
  where rest = neighbours x ([], es)


removeNode :: Eq a => a -> Graph a -> Graph a
removeNode x (ns, es)
  = (filter (/=x) ns, filter (\(a, b) -> x /= a && x /= b) es)

------------------------------------------------------
--
-- Part II
--

getMinNode :: (Ord a, Show a) => Graph a -> a
getMinNode g = snd $ minimumBy (comparing fst) [(b, a) | (a, b) <- degrees g]

colourGraph :: (Ord a, Show a) => Int -> Graph a -> Colouring a
colourGraph maxC g
  = colourGraph' [1..maxC] g
  where 
    colourGraph' :: (Ord a, Show a) => [Int] -> Graph a -> Colouring a
    colourGraph' _ ([], _) = []
    colourGraph' cs g
      | null availableColours = (n, 0) : cMap
      | otherwise             = (n, head availableColours) : cMap
      where 
        n = getMinNode g
        g' = (removeNode n g)
        availableColours = cs \\ (map ((flip lookUp) cMap) (neighbours n g))
        cMap = colourGraph' cs g'

------------------------------------------------------
--
-- Part III
--
buildIdMap :: Colouring Id -> IdMap
buildIdMap [] = [("return", "return")]
buildIdMap ((v, c):cl)
  | c == 0 = (v, v) : rest
  | otherwise = (v, 'R' : (show c)) : rest
  where rest = buildIdMap cl

buildArgAssignments :: [Id] -> IdMap -> [Statement]
buildArgAssignments [] idMap = []
buildArgAssignments (arg:args) idMap
  = (Assign (lookUp arg idMap) (Var arg)) : buildArgAssignments args idMap

renameExp :: Exp -> IdMap -> Exp
-- Pre: A precondition is that every variable referenced in 
-- the expression is in the idMap. 
renameExp k@(Const _) _ = k
renameExp (Var v) idM = Var (lookUp v idM)
renameExp (Apply op x1 x2) idM = Apply op (renameExp x1 idM) (renameExp x2 idM)

renameBlock :: Block -> IdMap -> Block
-- Pre: A precondition is that every variable referenced in 
-- the block is in the idMap. 
renameBlock b idM = filter (validAssignment) (map (renameStatement idM) b)
  where
    validAssignment :: Statement -> Bool
    validAssignment (Assign x (Var y)) = x /= y
    validAssignment _ = True 

    renameStatement :: IdMap -> Statement -> Statement
    renameStatement idM (Assign id exp)
      = Assign lhs rhs
      where 
        lhs = (lookUp id idM) 
        rhs = (renameExp exp idM)
    renameStatement idM (If exp b1 b2)
      = If (renameExp exp idM) (renameBlock b1 idM) (renameBlock b2 idM)
    renameStatement idM (While exp b)
      = While (renameExp exp idM) (renameBlock b idM)

renameFun :: Function -> IdMap -> Function
renameFun (f, as, b) idMap
  = (f, as, buildArgAssignments as idMap ++ renameBlock b idMap)

-----------------------------------------------------
--
-- Part IV
--

fastNub :: Ord a => [a] -> [a]
fastNub = S.toList . S.fromList

allPairs :: [a] -> [(a, a)]
allPairs xs = [(x, y) | (x:ys) <- tails xs, y <- ys]

buildIG :: [[Id]] -> IG
buildIG idss
  = (ns, es)
  where 
    ns = fastNub $ concat idss
    es = fastNub $ concatMap allPairs idss

-----------------------------------------------------
--
-- Part V
--
liveVars :: CFG -> [[Id]]
liveVars 
  = undefined

buildCFG :: Function -> CFG
buildCFG 
  = undefined
