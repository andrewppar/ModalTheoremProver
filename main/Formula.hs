module Formula
    (Formula (..)
    , equiv
    , parseFormula
    , makeAtom
    , atomicFormulaP
    , nonAtomicFormulaP
    , disjunctionP
    , conjunctionP
    , negationP
    , possibilityP
    , necessityP
    , joinStrings
    , atomicModalFormulaP
    , atomicPossibilityP
    , atomicNecessityP
    -- For Testing 
    , cleanFormulaString
    , getListItems
    , parseConjunctionString
    , parseImplicationString
    , parseNecessityString
    , getTopLevelItems
    , getTopLevelItemsInternal
    ) where

import Utilities
import Data.Maybe 
 -- * Propositional Language
data Formula = AtomicFormula {atom :: String}
             | And         {conjuncts :: [Formula]}
             | Or          {disjuncts :: [Formula]}
             | Implies     {antecedent :: Formula, consequent :: Formula}
             | Not         {negatum :: Formula}
             | Possibly    {possibility :: Formula}
             | Necessarily {necessity :: Formula}
               deriving (Eq)

-- Showing Formulas

instance Show Formula where
    show (AtomicFormula string) = show string ++ " "
    show (And conjuncts) = "(And " ++ (joinStrings " " . map show) conjuncts ++ ")"
    show (Or disjuncts)  = "(Or " ++  (joinStrings  " " . map show) disjuncts ++ ")"
    show (Implies antecedent consequent) = "(Implies " ++ (show antecedent) ++ (show consequent) ++ ")"
    show (Not negatum) = "(Not " ++ show negatum ++ ")"
    show (Possibly possibility) = "(M " ++ show possibility ++ ")"
    show (Necessarily necessity) = "(L " ++ show necessity ++ ")"

-- Reading Formulas

parseFormula :: String -> Maybe Formula 
parseFormula [] = Nothing 
parseFormula xs = 
  let cleanString = cleanFormulaString xs
      (formulaWord, rest) = splitFormulaWord cleanString
   in if rest == [] 
         then Nothing
      else if last rest /= ')'
              then Nothing 
           else 
              case formulaWord of 
                "AtomicFormula" -> parseAtomicFormula rest
                "And"           -> parseConjunctionString . init $ rest
                "Or"            -> parseDisjunctionString . init $ rest
                "Implies"       -> parseImplicationString . init $ rest
                "Not"           -> parseNegationString  . init $ rest
                "M"             -> parsePossibilityString  . init $ rest 
                "L"             -> parseNecessityString  . init $ rest
                otherwise -> Nothing

splitFormulaWord :: String -> (String, String)
splitFormulaWord (x:xs) = splitStringAtFirst ' ' xs

cleanFormulaString :: String -> String
cleanFormulaString string = 
  let specialBackwardChars = [' ', ')', ']']
      specialForwardChars = ['(', '[']
      almostClean =  snd $ foldr (\x (prev, result) -> 
                                   if x == ' ' && prev `elem` specialBackwardChars
                                      then (prev, result)
                                    else if x `elem` specialForwardChars && prev == ' '
                                            then ('(', x:(tail result))
                                          else (x, x:result)) (' ', []) string
   in if almostClean == [] 
         then [] 
      else if head almostClean == ' '
              then tail almostClean 
           else almostClean

parseAtomicFormula :: String -> Maybe Formula
parseAtomicFormula xs = 
  if filter(\x -> x /= ' ') xs /= xs
     then Nothing
  else let formula = init xs
        in Just (AtomicFormula formula)

parseConjunctionString :: String -> Maybe Formula 
parseConjunctionString = parseJunctionString "And"

parseDisjunctionString :: String -> Maybe Formula 
parseDisjunctionString = parseJunctionString "Or"

parseJunctionString :: String -> String -> Maybe Formula 
parseJunctionString junction xs = 
  if (head xs) /= '[' || (last xs) /= ']'
     then Nothing
  else let potentialArgs = map parseFormula . getListItems $ xs
        in if Nothing `elem` potentialArgs
              then Nothing
           else case junction of 
                  "And" -> Just (And (map Data.Maybe.fromJust potentialArgs))
                  "Or"  -> Just (Or  (map Data.Maybe.fromJust potentialArgs))

getListItems :: String -> [String]
getListItems [] = [] 
getListItems (x:xs) = getListItemsInternal 0 0 x xs "" []

getListItemsInternal :: Int -> Int -> Char -> String -> String -> [String] -> [String]
getListItemsInternal bracketCount parenCount char [] currentItem acc = acc ++ [currentItem]
getListItemsInternal 1 0 ',' (x:xs) currentItem acc = 
  getListItemsInternal 1 0 x xs "" (acc ++ [currentItem])
getListItemsInternal 1 0 ' ' (x:xs) currentItem acc =
  getListItemsInternal 1 0 x xs currentItem acc
getListItemsInternal 0 0 '[' (x:xs) currentItem acc =
  getListItemsInternal 1 0 x xs currentItem acc
getListItemsInternal 1 parenCount ']' (x:xs) currentItem acc = 
  getListItemsInternal 0 parenCount x xs currentItem acc 
getListItemsInternal bracketCount parenCount '[' (x:xs) currentItem acc =
  getListItemsInternal (bracketCount + 1) parenCount x xs (currentItem ++ ['[']) acc
getListItemsInternal bracketCount parenCount '(' (x:xs) currentItem acc =
  getListItemsInternal bracketCount (parenCount + 1) x xs (currentItem ++ ['(']) acc 
getListItemsInternal bracketCount parenCount ']' (x:xs) currentItem acc = 
  getListItemsInternal (bracketCount - 1) parenCount x xs (currentItem ++ [']']) acc 
getListItemsInternal bracketCount parenCount ')' (x:xs) currentItem acc = 
  getListItemsInternal bracketCount (parenCount - 1) x xs (currentItem ++ [')']) acc
getListItemsInternal bracketCount parenCount char (x:xs) currentItem acc = 
  getListItemsInternal bracketCount parenCount x xs (currentItem ++ [char]) acc

parseImplicationString :: String -> Maybe Formula
parseImplicationString xs = 
  let topLevelItems = getTopLevelItems xs 
   in if length topLevelItems /= 2 
         then Nothing
      else let args = map parseFormula topLevelItems 
            in if Nothing `elem` args
                  then Nothing
               else let antecedent = Data.Maybe.fromJust . head $ args
                        consequent = Data.Maybe.fromJust .  head . tail $ args
                     in Just (Implies antecedent consequent)


parseNegationString :: String -> Maybe Formula 
parseNegationString = parseUnaryFormulaString "Not"

parsePossibilityString :: String -> Maybe Formula 
parsePossibilityString = parseUnaryFormulaString "M"

parseNecessityString :: String -> Maybe Formula 
parseNecessityString = parseUnaryFormulaString "L"

parseUnaryFormulaString :: String -> String -> Maybe Formula 
parseUnaryFormulaString mainOperator xs = 
  let topLevelItems = getTopLevelItems xs
   in if length topLevelItems /= 1
         then Nothing
      else let potentialArgString = head topLevelItems 
               potentialArg = parseFormula potentialArgString 
            in if potentialArg == Nothing
                  then Nothing
               else case mainOperator of 
                      "Not" -> Just . Not . Data.Maybe.fromJust $ potentialArg
                      "M"   -> Just . Possibly . Data.Maybe.fromJust $ potentialArg
                      "L"   -> Just . Necessarily . Data.Maybe.fromJust $ potentialArg

getTopLevelItems :: String -> [String]
getTopLevelItems [] = []
getTopLevelItems (x:xs) = getTopLevelItemsInternal 0 x xs "" [] 

getTopLevelItemsInternal :: Int -> Char -> String -> String -> [String] -> [String]
getTopLevelItemsInternal _ char [] currentItem acc = acc ++ [currentItem ++ [char]]
getTopLevelItemsInternal 1 ')' (x:xs) currentItem acc = 
  getTopLevelItemsInternal 0 x xs "" (acc ++ [currentItem ++ [')']])
getTopLevelItemsInternal 0 '(' (x:xs) currentItem acc  = 
  getTopLevelItemsInternal 1 x xs (currentItem ++ ['(']) acc
getTopLevelItemsInternal 0 _ (x:xs) "" acc = getTopLevelItemsInternal 0 x xs [] acc
getTopLevelItemsInternal parenCount '(' (x:xs) currentItem acc  = 
  getTopLevelItemsInternal (parenCount + 1) x xs (currentItem ++ ['(']) acc
getTopLevelItemsInternal parenCount ')' (x:xs) currentItem acc  = 
  getTopLevelItemsInternal (parenCount - 1) x xs (currentItem ++ [')']) acc 
getTopLevelItemsInternal parenCount char (x:xs) currentItem acc =
  getTopLevelItemsInternal parenCount x xs (currentItem ++ [char]) acc 


---- Constructing Formulas

equiv :: Formula -> Formula -> Formula
equiv a b = (And [(Implies a b), (Implies b a)])

makeAtom :: String -> Formula
makeAtom string = AtomicFormula string

---- Predicates

atomicFormulaP :: Formula -> Bool
atomicFormulaP (AtomicFormula _) = True
atomicFormulaP _ = False

nonAtomicFormulaP :: Formula -> Bool
nonAtomicFormulaP = not . atomicFormulaP

disjunctionP :: Formula -> Bool
disjunctionP (Or _) = True
disjunctionP _ = False

conjunctionP :: Formula -> Bool
conjunctionP (And _) = True
conjunctionP _ = False

negationP :: Formula -> Bool
negationP (Not _) = True
negationP _ = False

possibilityP :: Formula -> Bool
possibilityP (Possibly _) = True
possibilityP _ = False

necessityP :: Formula -> Bool
necessityP (Necessarily _) = True
necessityP _ = False

possiblyFormulaDisjuncts :: Formula -> [Formula]
possiblyFormulaDisjuncts formula = possiblyFormulaJuncts disjunctionP disjuncts formula

possiblyFormulaConjuncts :: Formula -> [Formula]
possiblyFormulaConjuncts formula = possiblyFormulaJuncts conjunctionP conjuncts formula

possiblyFormulaJuncts :: (Formula -> Bool) -> (Formula -> [Formula]) ->  Formula -> [Formula]
--This is a weird function. I couldn't think of a more natural name than this either. It is meant to be used in our functions that transform a right disjunction or a left disjunction. Given a junctionP function it will either return all of the juncts of the input formula or the list containing the original formula.
possiblyFormulaJuncts junctionFunction gatherFunction formula = if junctionFunction formula
                                                                then gatherFunction formula
                                                                else [formula]


-- @todo Test this function
atomicModalFormulaP :: Formula -> Bool
atomicModalFormulaP form = atomicPossibilityP form || atomicNecessityP form

atomicPossibilityP :: Formula -> Bool
atomicPossibilityP = atomicModalPInt Possible

atomicNecessityP :: Formula -> Bool
atomicNecessityP = atomicModalPInt Necessary


data ModalType = Possible | Necessary deriving (Eq)

atomicModalPInt :: ModalType -> Formula -> Bool
atomicModalPInt _ (AtomicFormula _) = False
atomicModalPInt _ (And _) = False
atomicModalPInt _ (Or  _) = False
atomicModalPInt _ (Implies _ _) = False
atomicModalPInt _ (Not _) = False
atomicModalPInt modalType (Necessarily p) = case modalType of
                                             Necessary -> atomicFormulaP p
                                             Possible -> False
atomicModalPInt modalType (Possibly p) = case modalType of
                                          Necessary -> False
                                          Possible -> atomicFormulaP p
