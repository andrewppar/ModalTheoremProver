module Hypersequent
    (Hypersequent (..)
    , showHypersequent 
    , hypersequentClosed
    , atomicHypersequent
    , hypersequentRemoveDuplicates
) where

import Utilities
import Formula
import Canonicalizer
import Sequent

data Hypersequent = World Sequent [Hypersequent] deriving (Eq)

instance Show Hypersequent where
  show = showHypersequent True 0 0


showHypersequent :: Bool -> Int -> Int -> Hypersequent -> String 
showHypersequent firstPass depth padding (World seq hypers) = 
  let paddingPrefix = if firstPass 
                         then makePrefix 0 " "
                      else makePrefix padding " "
      depthPrefix  = makePrefix depth "|"
      tag = "- "  
      line = paddingPrefix ++ depthPrefix ++ tag ++ (show seq) ++ "\n"
      recursiveCase = mapAppend (showHypersequent False (depth + 1) padding) hypers
   in line ++ recursiveCase 

hypersequentClosed :: Hypersequent -> Bool 
hypersequentClosed (World seq hypers) = 
  let intersection  = setIntersection  (posFormulas seq) . negFormulas $ seq 
      closed = intersection /= [] 
   in case closed of 
     True -> True 
     False -> if hypers == [] 
                 then False 
              else not .
                   emptyListP .  
                   filter (\bool -> bool == True) .
                   map hypersequentClosed $ hypers 

atomicHypersequent :: Hypersequent -> Bool 
atomicHypersequent (World seq hypers) = 
  if atomicSequentP seq
     then let 
        nonAtomicHypers = filter (\bool -> bool /= True) .
                          map atomicHypersequent $ hypers
           in nonAtomicHypers == [] 
  else False

hypersequentRemoveDuplicates :: Hypersequent -> Hypersequent
hypersequentRemoveDuplicates (World seq hypers) = 
  let newSeq = (sequentRemoveDuplicates seq)
      newHypers = (map hypersequentRemoveDuplicates hypers)
   in World newSeq newHypers 
