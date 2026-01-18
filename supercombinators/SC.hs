module SC where

import Data.List
import Data.Maybe

import Types
import Examples

---------------------------------------------------------

prims :: [Id]
prims
  = ["+", "-", "*", "<=", "ite"]

lookUp :: Id -> [(Id, a)] -> a
lookUp v env
  = fromMaybe (error ("lookUp failed with search key " ++ v))
              (lookup v env)

---------------------------------------------------------
-- Part I

isFun :: Exp -> Bool
isFun (Fun _ _) = True
isFun _ = False

splitDefs :: [Binding] -> ([Binding], [Binding])
splitDefs = partition (isFun . snd)

topLevelFunctions :: Exp -> Int
topLevelFunctions (Let bs _) = length $ filter (isFun . snd) bs
topLevelFunctions _ = 0

---------------------------------------------------------
-- Part II

unionAll :: Eq a => [[a]] -> [a]
unionAll = foldr union []

freeVars :: Exp -> [Id]
freeVars (Const _) = []
freeVars (Var id)
  | elem id prims = []
  | otherwise     = [id]
freeVars (App f ps) = union (freeVars f) (unionAll $ map freeVars ps)
freeVars (Fun ps e) = (freeVars e) \\ ps
freeVars (Let bs e) = (unionAll $ map freeVars (e:bes)) \\ bvs
  where 
    (bvs, bes) = (unzip bs)

---------------------------------------------------------
-- Part III

-- Given...
lambdaLift :: Exp -> Exp
lambdaLift e
  = lift (modifyFunctions (buildFVMap e) e)

buildFVMap :: Exp -> [(Id, [Id])]
buildFVMap (Let bs e)
  = (map (\(n, d) -> (n, fvs)) fs) 
  ++ (buildFVMap e) 
  ++ (concatMap buildFVMap ds)
  where 
    fs = fst $ splitDefs bs
    (ns, ds) = unzip fs
    fvs = sort $ (unionAll $ map freeVars ds) \\ ns
buildFVMap (Fun _ e) = buildFVMap e
buildFVMap _ = []

modifyFunctions :: [(Id, [Id])] -> Exp -> Exp
-- Pre: The mapping table contains a binding for every function
-- named in the expression.
modifyFunctions fvM (Let bs e) 
  = Let (modifyFunctions' fvM bs) (modifyFunctions fvM e)
  where
    modifyFunctions' :: [(Id, [Id])] -> [Binding] -> [Binding]
    modifyFunctions' _ [] = []
    modifyFunctions' fvM ((f, Fun as e'):bs) 
      = (('$':f), Fun ((lookUp f fvM) ++ as) (modifyFunctions fvM e')) 
      : (modifyFunctions' fvM bs)
    modifyFunctions' fvM (b:bs) = b : (modifyFunctions' fvM bs)
modifyFunctions fvM v@(Var id)  
  | elem id (map fst fvM) 
    = if null fvs 
      then Var id' 
      else App (Var id') fvs
  | otherwise = v
  where 
    fvs = map Var (lookUp id fvM)
    id' = ('$':id)
modifyFunctions fvM (App e es) 
  = App (modifyFunctions fvM e) (map (modifyFunctions fvM) es)
modifyFunctions _ e = e

-- The default definition here is id.
-- If you implement the above two functions but not this one
-- then lambdaLift above will remove all the free variables
-- in functions; it just won't do any lifting.
lift :: Exp -> Exp
lift e = Let cs e'
  where (e', cs) = lift' e 

-- You may wish to use this...
lift' :: Exp -> (Exp, [Supercombinator])
lift' (Let bs e)
  = (e', bs ++ cs)
  where (e', cs) = lift' e
lift' exp@(Let bs e)