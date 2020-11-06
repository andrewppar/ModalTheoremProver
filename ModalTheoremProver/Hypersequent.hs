module ModalTheoremProver.Hypersequent
    (Hypersequent (..)
    , Serialization (..)
    , serializeHypersequent
    , showHypersequent 
    , hypersequentClosed
    , atomicHypersequent
    , hypersequentRemoveDuplicates
) where

import ModalTheoremProver.Utilities
import ModalTheoremProver.Formula
import ModalTheoremProver.Canonicalizer
import ModalTheoremProver.Sequent

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

data Serialization = HTML | HS

serializeHypersequent :: Serialization -> Hypersequent -> String
serializeHypersequent HTML = serializeHypersequentAsHtml 
serializeHypersequent HS   = serializeHypersequentAsHaskell

serializeHypersequentAsHtml :: Hypersequent -> String 
serializeHypersequentAsHtml hypersequent =
  let divStart = "<div class=\"hypersequent\">\n" 
      html = serializeHypersequentAsHtmlInternal hypersequent
      divEnd = "\n</div>"
   in divStart ++ html ++ divEnd

serializeHypersequentAsHtmlInternal :: Hypersequent -> String 
serializeHypersequentAsHtmlInternal (World seq hypers) = 
  let listStart = "<ul>\n" 
      sequent = "<li>" ++ (show seq) ++ "</li>" ++ "\n"
      recursiveCase =
        foldr (\serialized acc -> acc ++ serialized) ""  . map serializeHypersequentAsHtmlInternal $ hypers
      listEnd = "\n</ul>"
   in listStart ++ sequent ++ recursiveCase ++ listEnd

serializeHypersequentAsHaskell :: Hypersequent -> String 
serializeHypersequentAsHaskell (World (Sequent negs poss) hypers) = 
  let negatives = joinStrings "," . map serializeFormulaAsHaskell $ negs
      positives = joinStrings "," . map serializeFormulaAsHaskell $ poss
      seq = "(makeSequent [" ++ negatives ++ "]" ++ "  [" ++ positives ++ "])"
      recCase = joinStrings "," . map serializeHypersequentAsHaskell $ hypers
   in "(World " ++ seq ++ "[" ++ recCase ++ "])"
     

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
