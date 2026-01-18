module Tries where

import Data.List hiding (insert)
import Data.Bits

import Types
import HashFunctions
import Examples

--------------------------------------------------------------------
-- Part I

-- Use this if you're counting the number of 1s in every
-- four-bit block...
bitTable :: [Int]
bitTable
  = [0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4]

countOnes :: Int -> Int
countOnes 0 = 0
countOnes n
  = (bitTable !! r) + (countOnes q)
    where (q, r) = divMod n 16

countOnesFrom :: Int -> Int -> Int
countOnesFrom i n
  = countOnes (n .&. (bit i - 1))

getIndex :: Int -> Int -> Int -> Int
getIndex n i s
  = shiftR (n .&. mask) (msb - s)
    where 
      msb = (i + 1) * s
      mask = (bit msb) - 1

-- Pre: the index is less than the length of the list
replace :: Int -> [a] -> a -> [a]
replace 0 (_:xs) v = v : xs
replace n (x:xs) v
  = x : replace (n - 1) xs v

-- Pre: the index is less than or equal to the length of the list
insertAt :: Int -> a -> [a] -> [a]
insertAt 0 v xs = v : xs
insertAt n v (x:xs)
  = x : insertAt (n - 1) v xs

--------------------------------------------------------------------
-- Part II

sumTrie :: (Int -> Int) -> ([Int] -> Int) -> Trie -> Int
sumTrie _ g (Leaf xs) = g xs
sumTrie f g (Node _ n) = sum $ map (sumNode f g) n

sumNode :: (Int -> Int) -> ([Int] -> Int) -> SubNode -> Int
sumNode f _ (Term x) = f x
sumNode f g (SubTrie t) = sumTrie f g t

--
-- If you get the sumTrie function above working you can uncomment
-- these three functions; they may be useful in testing.
--
trieSize :: Trie -> Int
trieSize t
  = sumTrie (const 1) length t

binCount :: Trie -> Int
binCount t
  = sumTrie (const 1) (const 1) t

meanBinSize :: Trie -> Double
meanBinSize t
  = fromIntegral (trieSize t) / fromIntegral (binCount t)

member :: Int -> Hash -> Trie -> Int -> Bool
member = goTrie 0
  where 
    goTrie :: Int -> Int -> Hash -> Trie -> Int -> Bool
    goTrie l k h (Leaf xs) s = k == xs !! i
      where i = getIndex h l s
    goTrie l k h (Node bv xs) s
      | testBit bv i = goNode (l + 1) k h (xs !! n) s
      | otherwise    = False
      where 
        i = getIndex h l s
        n = countOnesFrom i bv

    goNode :: Int -> Int -> Hash -> SubNode -> Int -> Bool
    goNode _ k _ (Term v) _ = k == v
    goNode l k h (SubTrie t) s
      = goTrie l k h t s

--------------------------------------------------------------------
-- Part III

insert :: HashFun -> Int -> Int -> Int -> Trie -> Trie
insert hf md s v t = goTrie 0 (hf v) hf md s v t
  where
    goTrie :: Int -> Int -> HashFun -> Int -> Int -> Int -> Trie -> Trie
    goTrie l h hf md s v t@(Leaf xs)
      | elem v xs        = t
      | otherwise        = Leaf (v : xs)
    goTrie l h hf md s v (Node bv xs)
      | l == md - 1  = Leaf [v]
      | testBit bv i = Node bv (replace n xs (newNode (l + 1) h hf md s v (xs !! n)))
      | otherwise    = Node (setBit bv i) (insertAt n (Term v) xs)
      where 
        i = getIndex h l s
        n = countOnesFrom i bv

    newNode :: Int -> Int -> HashFun -> Int -> Int -> Int -> SubNode -> SubNode
    newNode l h hf md s v n@(Term v')
      | v == v'   = n
      | otherwise = SubTrie (goTrie l h hf md s v 
                              (goTrie l h' hf md s v' empty))
      where h' = hf v'
    newNode l h hf md s v (SubTrie t)
      = SubTrie (goTrie l h hf md s v t)

buildTrie :: HashFun -> Int -> Int -> [Int] -> Trie
buildTrie hf md s xs
  = foldr (\x t -> insert hf md s x t) empty xs
