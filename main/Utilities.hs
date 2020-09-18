module Utilities
    (myTail
    , setIntersection
    , emptyListP
    , append
    , mapAppend
    , generalizedConjunction
    , generalizedDisjunction
    , anyInListMeetsCriteria
    , everyInListMeetsCriteria
    , cartesianProduct
    , removeDuplicates
    , listsOverlapP
    , replaceItemAtIndex
    , range
    , quickSort
    , snoc
    , slowRemoveDuplicates
    , splitStringAtFirst 
    , conjoinedWith
    , joinStrings) where

import Control.Parallel
import Control.Parallel.Strategies

myTail :: [a] -> [a]
myTail [] = []
myTail (_:xs) = xs

setIntersection :: (Eq a) => [a] -> [a] -> [a]
setIntersection xs ys = foldr (\x acc -> if (elem x ys) then x:acc else acc) [] xs

emptyListP :: [a] -> Bool
emptyListP [] = True
emptyListP _  = False

append :: [a] -> [a] -> [a]
append xs ys = foldr (\x acc -> x:acc) ys xs -- @note: this reverses the order of the xs

mapAppend :: (a -> [b]) -> [a] -> [b]
mapAppend f xs = foldr (\x acc -> x ++ acc) [] $ map f xs

generalizedConjunction :: [Bool] -> Bool
generalizedConjunction = generalizedJunction True (&&)

generalizedDisjunction :: [Bool] -> Bool
generalizedDisjunction = generalizedJunction False (||)

generalizedJunction :: Bool  -> (Bool -> Bool -> Bool) -> [Bool] -> Bool
generalizedJunction base _ [] = base
generalizedJunction base booleanFunction (x:xs) =
                      (booleanFunction x (generalizedJunction base booleanFunction xs))



anyInListMeetsCriteria :: (a -> Bool) -> [a] -> Bool
anyInListMeetsCriteria f = generalizedDisjunction . map f

everyInListMeetsCriteria :: (a -> Bool) -> [a] -> Bool
everyInListMeetsCriteria f = generalizedConjunction . map f


addEachToEachInList :: [a] -> [[a]] -> [[a]] --We use this in the canonoicalizer, but I bet it's wrong probably it should be addToEach, changing it doesn't cause any tests to fail. @todo investigate
addEachToEachInList xs [] = [xs]
addEachToEachInList xs (y:ys) =
    let newAdditions = map (:y) xs
    in  newAdditions ++ (addEachToEachInList xs ys)



cartesianProduct :: [[a]] -> [[a]]  -- @todo make this recursive
cartesianProduct [] = []
cartesianProduct [xs] = map (\x -> [x]) xs
cartesianProduct (x:xs) =
    let recursiveCase = cartesianProduct xs
    in addToEach x recursiveCase

addToEach :: [a] -> [[a]] -> [[a]]
addToEach _ [] = []
addToEach xs (y:ys) =
    let newAdditions = map (:y) xs
    in  newAdditions ++ (addToEach xs ys)

addToEachWithBase :: [a] -> [[a]] -> [[a]]
addToEachWithBase [] ys = ys
addToEachWithBase xs [] = [xs]
addToEachWithBase (x:xs) ys =
    let recursiveCase = addToEachWithBase xs ys
    in  map (x:) recursiveCase

removeDuplicates :: (Eq a) => [a] -> [a]
removeDuplicates [] = []
removeDuplicates (x:[]) = [x]
removeDuplicates (x:y:zs) = if x == y
                            then (y:(removeDuplicates zs))
                            else (x: (removeDuplicates (y:zs)))

listsOverlapP :: (Eq a) => (a -> a -> Bool) -> [a] -> [a] -> Bool
listsOverlapP sortingFunction xs ys =
    sortableListsOverlapP
    sortingFunction (quickSort sortingFunction xs) (quickSort sortingFunction ys)

sortableListsOverlapP :: (Eq a) =>  (a -> a -> Bool) -> [a] -> [a] -> Bool
-- Note: This function assumes that the lists you passed it are sorted.
sortableListsOverlapP _ _ [] = False
sortableListsOverlapP _ [] _ = False
sortableListsOverlapP sortingFunction theXs@(x:xs) theYs@(y:ys)
    | x == y = True
    | sortingFunction x y = sortableListsOverlapP sortingFunction xs theYs
    | otherwise = sortableListsOverlapP sortingFunction theXs ys

replaceItemAtIndex :: a -> [a] -> Int -> [a]
replaceItemAtIndex item [] _ = []
replaceItemAtIndex y (x:xs) 0 = (y:xs)
replaceItemAtIndex y (x:xs) n =  (x:replaceItemAtIndex y xs (n - 1))

removeItemAtIndex :: Int -> [a] -> [a]
removeItemAtIndex _ [] = []
removeItemAtIndex 0 (x:xs) = xs
removeItemAtIndex n (x:xs) = x:(removeItemAtIndex (n - 1) xs)

range :: Int -> [Int]
range num = [0..num]

snoc :: a -> [a] -> [a]
snoc x [] = [x]
snoc x (y:ys) = y:(snoc x ys)

quickSort :: (Eq a) => (a -> a -> Bool) -> [a] -> [a]
quickSort _ [] = []
quickSort sortingFunction (x:xs) =
    let smaller = quickSort sortingFunction [y | y <- xs, sortingFunction y x]
        bigger  = quickSort sortingFunction [y | y <- xs, not (sortingFunction y x)]
    in smaller ++ (x:bigger)


slowRemoveDuplicates :: (Eq a) => [a] -> [a]
-- We need a sorting function to optimize this.
slowRemoveDuplicates [] = []
slowRemoveDuplicates (x:xs) = if x `elem` xs
                              then slowRemoveDuplicates xs
                              else x:slowRemoveDuplicates xs


conjoinedWith :: (a  -> Bool) -> (a -> Bool) -> a -> Bool
conjoinedWith f1 f2 item = f1 item && f2 item


splitStringAtFirst :: Char -> String -> (String, String)
splitStringAtFirst char [] = ([], [])
splitStringAtFirst char (x:xs) = 
  if x == char 
     then ([], xs)
  else 
     let (first, second)  = splitStringAtFirst char xs 
      in (x:first, second)

joinStrings :: String -> [String] -> String
joinStrings _ [] = " "
joinStrings stringToInsert (x:xs) = x ++ (foldl (\string accumulator -> string ++ stringToInsert ++  accumulator) "" xs)


{-| Parallel Experiment |-}

parallelMap :: (a -> b) -> [a] -> [b]
parallelMap _ [] = []
parallelMap f (x:xs) = par a (pseq b (a:b))
    where a = f x
          b = parallelMap f xs


badFib :: Int -> Int
badFib 0 = 1
badFib 1 = 1
badFib n =  a +  b
    where a = (badFib (n - 2))
          b = (badFib (n - 1))


check1 = (parMap rdeepseq) badFib (replicate 5 40)
check2 = map badFib (replicate 5 40)
