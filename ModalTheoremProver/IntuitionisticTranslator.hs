module ModalTheoremProver.IntuitionisticTranslator
  (intuitionisticTranslate) where 

import ModalTheoremProver.Formula 
import Data.Maybe 

intuitionisticTranslate :: Formula -> Maybe Formula
intuitionisticTranslate f@(AtomicFormula _) = Just (Necessarily f)
intuitionisticTranslate (And fs) = translateJunction "And" fs
intuitionisticTranslate (Or fs) = translateJunction "Or" fs
intuitionisticTranslate (Implies ant cons) = 
  Just (Necessarily (Implies (Data.Maybe.fromJust (intuitionisticTranslate ant)) (Data.Maybe.fromJust (intuitionisticTranslate cons))))
intuitionisticTranslate (Equivalent one two) = 
  let maybeOne = Data.Maybe.fromJust . intuitionisticTranslate $ one
      maybeTwo = Data.Maybe.fromJust . intuitionisticTranslate $ two
   in if maybeOne == maybeTwo
         then Just (Necessarily (Implies (AtomicFormula "p") (AtomicFormula "p")))
         else Just (And  [ (Necessarily (Implies maybeOne maybeTwo))
                 , (Necessarily (Implies maybeTwo maybeOne)) ])
intuitionisticTranslate (Not f) = 
  Just (Necessarily (Not (Data.Maybe.fromJust (intuitionisticTranslate f))))
intuitionisticTranslate (Possibly _) = Nothing
intuitionisticTranslate (Necessarily _) = Nothing

translateJunction :: String -> [Formula] -> Maybe Formula 
translateJunction junctionType fs = 
  let possiblyTranslated = map intuitionisticTranslate fs
   in if (filter (\x -> x == Nothing) possiblyTranslated) == [] 
         then case junctionType of  --TODO Replace these strings with some other type
                "Or" -> Just (Or (map Data.Maybe.fromJust possiblyTranslated))
                "And" -> Just (And (map Data.Maybe.fromJust possiblyTranslated))
                otherwise  -> Nothing
      else Nothing
