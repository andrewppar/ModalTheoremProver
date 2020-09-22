module IntuitionisticTranslator
  (intuitionisticTranslate) where 

import Formula 
import Data.Maybe 

intuitionisticTranslate :: Formula -> Maybe Formula
intuitionisticTranslate f@(AtomicFormula _) = Just (Necessarily f)
intuitionisticTranslate (And fs) = translateJunction "And" fs
intuitionisticTranslate (Or fs) = translateJunction "Or" fs
intuitionisticTranslate (Implies ant cons) = 
  Just (Necessarily (Implies (Data.Maybe.fromJust (intuitionisticTranslate ant)) (Data.Maybe.fromJust (intuitionisticTranslate cons))))
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
