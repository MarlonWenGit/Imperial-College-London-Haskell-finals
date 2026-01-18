module Int where

import Types
import Examples
import Utilities

import Data.Maybe

addP :: Polynomial -> Polynomial -> Polynomial
addP p1 [] = p1
addP [] p2 = p2
addP p1@((c1, e1):ts1) p2@((c2, e2):ts2)
  | e1 == e2  = (c1 + c2, e1) : (addP ts1 ts2)
  | e1 < e2   = (c2, e2) : (addP p1 ts2)
  | otherwise = (c1, e1) : (addP ts1 p2)

mulP :: Polynomial -> Polynomial -> Polynomial
mulP p1 p2 = foldr addP [] (map (mulT p1) p2)
  where 
    mulT :: Polynomial -> Term -> Polynomial
    mulT [] _ = []
    mulT ((c1, e1):p1) t@(c2, e2) 
      = (c1 * c2, e1 + e2) : (mulT p1 t)

sumP :: [Polynomial] -> Polynomial
sumP = foldr addP []

prodP :: [Polynomial] -> Polynomial
prodP = foldr mulP [(1, 0)]

diffT :: Term -> Term 
diffT (_, 0) = (0, 0)
diffT (c, e) = (c * (fromInteger e), e - 1)

intT :: Term -> Term
intT (c, e) = (c / (fromInteger e'), e')
  where e' = e + 1

diffP :: Polynomial -> Polynomial
diffP = map (diffT)

intP :: Polynomial -> Polynomial
intP = map (intT)

toExpr :: Rational -> Expr
toExpr n = P [(n, 0)]

diffE :: Expr -> Expr
diffE (P p) = P (diffP p)
diffE (Add e1 e2) = Add (diffE e1) (diffE e2)
diffE (Mul e1 e2) = Add (Mul e1 e2') (Mul e1' e2)
  where 
    e1' = diffE e1
    e2' = diffE e2 
diffE (Pow e r) = Mul (diffE e) (Mul (toExpr r) (Pow e (r - 1)))
diffE (Log e) = Mul (diffE e) (Pow e (-1))

isConstant :: Expr -> Bool
isConstant (P [(_, 0)]) = True
isConstant _ = False

intE :: Expr -> Maybe Expr
intE (P p) = Just $ P (intP p)
intE (Add e1 e2) 
  | (null i1) || (null i2) = Nothing
  | otherwise              = Just $ Add (fromJust i1) (fromJust i2)
  where 
    i1 = (intE e1)
    i2 = (intE e2)
intE (Mul e1 e2) 
  | (isConstant e1) && (not (null i2)) = Just $ Mul e1 (fromJust i2)
  | (isConstant e2) && (not (null i1)) = Just $ Mul e2 (fromJust i1)
  | not (null m1) = m1
  | not (null m2) = m2
  | otherwise     = Nothing
  where 
    i2 = (intE e2)
    i1 = (intE e1)

    m1 = applyICR e1 e2
    m2 = applyICR e2 e1

intE e = applyICR (Mul (toExpr 1) e)

applyICR :: Expr -> Expr -> Maybe Expr
applyICR e1 e2@(Pow u r)
    | e1 == (diffE u) = if r /= -1 then Just $ Mul (Pow u r') (toExpr (1/r'))
                        else Just $ Log u
    | otherwise       = Nothing
    where r' = r + 1
applyICR e1 e2@(Log u)
    | e1 == (diffE u) = Just $ Mul u (Add (Log u) (toExpr (-1)))
    | otherwise       = Nothing
applyICR e1 e2
    | e1 == (diffE e2) = Just $ Mul (Pow e2 2) (toExpr (1/2))
    | otherwise       = Nothing
