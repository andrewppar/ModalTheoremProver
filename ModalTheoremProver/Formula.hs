module ModalTheoremProver.Formula
    (Formula (..)
    , equiv
    , parseFormula
    , serializeFormulaAsHaskell
    , makeAtom
    , atomicFormulaP
    , nonAtomicFormulaP
    , implicationP
    , disjunctionP
    , conjunctionP
    , negationP
    , possibilityP
    , necessityP
    , joinStrings
    , atomicModalFormulaP
    , atomicPossibilityP
    , atomicNecessityP
    , formulaLessThan
    , getAtomicsInFormula
    , cleanFormulaString
    , getListItems
    , parseConjunctionString
    , parseImplicationString
    , parseNecessityString
    , getTopLevelItems
    , getTopLevelItemsInternal
    , sortFormulas
    ) where

import ModalTheoremProver.Utilities
import Data.Maybe
import Data.Char


 -- * Propositional Language
data Formula = AtomicFormula {atom :: String}
             | And         {conjuncts :: [Formula]}
             | Or          {disjuncts :: [Formula]}
             | Implies     {antecedent :: Formula, consequent :: Formula}
             | Equivalent  {first :: Formula, second :: Formula}
             | Not         {negatum :: Formula}
             | Possibly    {possibility :: Formula}
             | Necessarily {necessity :: Formula}
               deriving (Eq)

instance Ord Formula where
  (<=) = formulaLessThanOrEqual
  (<) = formulaLessThan
  x > y =  not (formulaLessThanOrEqual x y)
  x >= y = not (formulaLessThan x  y)
  max form1 form2 = if  (form1 < form2) then form2 else form1
  min form1 form2 = if  (form1 > form2) then form2 else form1

sortFormulas :: [Formula] -> [Formula]
sortFormulas = quickSort formulaLessThanOrEqual

formulaLessThanOrEqual :: Formula -> Formula -> Bool
formulaLessThanOrEqual formulaOne formulaTwo =
    formulaOne == formulaTwo || formulaLessThan formulaOne formulaTwo

formulaLessThan :: Formula -> Formula -> Bool
formulaLessThan formulaOne formulaTwo =
    let rankOne = formulaRank formulaOne
        rankTwo = formulaRank formulaTwo
     in if rankOne Prelude.< rankTwo
        then True
        else if rankOne == rankTwo
             then complexFormulaLessThan formulaOne formulaTwo
             else False

formulaRank :: Formula -> Int
formulaRank (Not negatum)      = 1 + (formulaRank negatum)
formulaRank (Implies ant cons) = (formulaRank ant) + (formulaRank cons)
formulaRank (Equivalent one two) = (formulaRank one) + (formulaRank two)
formulaRank (And conjuncts)    = sum . (map formulaRank) $ conjuncts
formulaRank (Or disjuncts)      = sum . (map formulaRank) $ disjuncts
formulaRank (Necessarily necessity) = 1 + (formulaRank necessity)
formulaRank (Possibly possibility) = 1 + (formulaRank possibility)
formulaRank (AtomicFormula str) = 1

stringLessThan :: String -> String -> Bool
stringLessThan [] _ = True
stringLessThan _ [] = False
stringLessThan (x:xs) (y:ys) = if charLessThan x y
                               then True
                               else False

charLessThan :: Char -> Char -> Bool
charLessThan c1 c2 =
    let c1Number = alphabeticNumber alphabeticOrderAList c1
        c2Number = alphabeticNumber alphabeticOrderAList c2
    in c1Number < c2Number

alphabeticNumber :: [(Char,Int)] -> Char -> Int
alphabeticNumber [] char = 100
alphabeticNumber ((testChar,int):alist) char = if char == testChar
                                               then int
                                               else alphabeticNumber alist char

alphabeticOrderAList :: [(Char,Int)]
alphabeticOrderAList =
    let downcaseAlphabet = "abcdefghijklmnopqrstuvwxyz"
        upcaseAlphabet   = map toUpper downcaseAlphabet
        numbers          = "0123456789"
        allChars         = append downcaseAlphabet (append upcaseAlphabet numbers)
    in zip allChars [1..]

complexFormulaLessThan :: Formula -> Formula -> Bool
complexFormulaLessThan (AtomicFormula atomOne) (AtomicFormula atomTwo) =
    stringLessThan atomOne atomTwo
complexFormulaLessThan (AtomicFormula atom) _ = True

complexFormulaLessThan (Not negatum1) (Not negatum2) = complexFormulaLessThan negatum1 negatum2
complexFormulaLessThan (Not negatum1) _ = True

complexFormulaLessThan (Implies ant1 con1) (Implies ant2 con2) = complexFormulaLessThan ant1 ant2
complexFormulaLessThan (Implies ant con) (Not negatum) = False
complexFormulaLessThan (Implies ant con) _ = True

complexFormulaLessThan (Equivalent one two) (Equivalent three four) = complexFormulaLessThan one three
complexFormulaLessThan (Equivalent _ _) (Not _) = False
complexFormulaLessThan (Equivalent _ _) (Implies _ _) = False
complexFormulaLessThan (Equivalent _ _) _ = True

complexFormulaLessThan (And conjunctsOne) (And conjunctsTwo) =
    compareJuncts conjunctsOne conjunctsTwo
complexFormulaLessThan (And conjuncts) (Not negatum) = False
complexFormulaLessThan (And conjuncts) (Implies ant con) = False
complexFormulaLessThan (And conjuncts) _ = True

complexFormulaLessThan (Or disjunctsOne) (Or disjunctsTwo) =
    compareJuncts disjunctsOne disjunctsTwo
complexFormulaLessThan (Or disjuncts) (Not negatum) = False
complexFormulaLessThan (Or disjuncts) (Implies ant con) = False
complexFormulaLessThan (Or disjuncts) (And conjuncts) = False
complexFormulaLessThan (Or disjuncts) _ = True

complexFormulaLessThan (Necessarily necessity1) (Necessarily necessity2) =
    complexFormulaLessThan necessity1 necessity2
complexFormulaLessThan (Necessarily necessity) (Not negatum) = False
complexFormulaLessThan (Necessarily necessity) (Implies ant con) = False
complexFormulaLessThan (Necessarily necessity) (And conjuncts) = False
complexFormulaLessThan (Necessarily necessity) (Or disjuncts) = False
complexFormulaLessThan (Necessarily necessity) _ = True

complexFormulaLessThan (Possibly possibility1) (Possibly possibility2) =
    complexFormulaLessThan possibility1 possibility2
complexFormulaLessThan (Possibly possibility) (Not negatum) = False
complexFormulaLessThan (Possibly possibility) (Implies ant con) = False
complexFormulaLessThan (Possibly possibility) (And conjuncts) = False
complexFormulaLessThan (Possibly possibility) (Or disjuncts) = False
complexFormulaLessThan (Possibly possibility) (Necessarily necessity) = False
complexFormulaLessThan (Possibly possibility) _ = True

compareJuncts :: [Formula] -> [Formula] -> Bool
compareJuncts conjunctsOne conjunctsTwo =
    let sortedOne = sortFormulas conjunctsOne
        sortedTwo = sortFormulas conjunctsTwo
    in  compareListsByFunction complexFormulaLessThan sortedOne sortedTwo



-- Showing Formulas

instance Show Formula where
    show (AtomicFormula string) = string 
    show (And conjuncts) = "(And " ++ (joinStrings " " . map show) conjuncts ++ ")"
    show (Or disjuncts)  = "(Or " ++  (joinStrings  " " . map show) disjuncts ++ ")"
    show (Implies antecedent consequent) = "(Implies " ++ (show antecedent) ++ " " ++ (show consequent) ++ ")"
    show (Equivalent formulaOne formulaTwo) = "(Equivalent  " ++ (show formulaOne) ++  " " ++  (show formulaTwo) ++ ")"
    show (Not negatum) = "(Not " ++ show negatum ++ ")"
    show (Possibly possibility) = "(M " ++ show possibility ++ ")"
    show (Necessarily necessity) = "(L " ++ show necessity ++ ")"

serializeFormulaAsHaskell :: Formula -> String
serializeFormulaAsHaskell (AtomicFormula string) =
  "(AtomicFormula " ++ show string ++ ")"
serializeFormulaAsHaskell (Not negatum) =
  "(Not " ++ serializeFormulaAsHaskell negatum ++ ")"
serializeFormulaAsHaskell (And conjuncts) =
  let  prefix  = "(And ["
       middle = joinStrings "," . map serializeFormulaAsHaskell $ conjuncts
       postfix = "])"
   in prefix ++ middle ++ postfix
serializeFormulaAsHaskell (Or disjuncts) =
   let  prefix  = "(Or ["
        middle = joinStrings "," . map serializeFormulaAsHaskell $ disjuncts
        postfix = "])"
   in prefix ++ middle ++ postfix
serializeFormulaAsHaskell (Implies antecedent consequent) =
  joinStrings "" [ "(Implies "
                 , serializeFormulaAsHaskell antecedent
                 , serializeFormulaAsHaskell consequent
                 , ")"]
serializeFormulaAsHaskell (Equivalent one two) =
  joinStrings "" [ "(Equivalent "
                 , serializeFormulaAsHaskell one
                 , serializeFormulaAsHaskell two
                 , ")"]
serializeFormulaAsHaskell (Necessarily necessity) =
  "(Necessarily " ++ serializeFormulaAsHaskell necessity ++ ")"
serializeFormulaAsHaskell (Possibly possibility) =
  "(Possibly " ++ serializeFormulaAsHaskell possibility ++ ")"



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
                "Equivalent"    -> parseBiconditionalString . init $ rest
                "Not"           -> parseNegationString  . init $ rest
                "M"             -> parsePossibilityString  . init $ rest
                "L"             -> parseNecessityString  . init $ rest
                otherwise -> Just (AtomicFormula "Fuck Off")

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
parseImplicationString = parseBinaryFormulaString "Implies"

parseBiconditionalString :: String  -> Maybe Formula
parseBiconditionalString = parseBinaryFormulaString "Equivalent"

parseBinaryFormulaString :: String -> String  -> Maybe Formula
parseBinaryFormulaString parseType xs =
  let topLevelItems = getTopLevelItems xs
   in if length topLevelItems /= 2
         then Nothing
      else let args = map parseFormula topLevelItems
            in if Nothing `elem` args
                  then Nothing
               else let antecedent = Data.Maybe.fromJust . head $ args
                        consequent = Data.Maybe.fromJust .  head . tail $ args
                     in case  parseType of
                       "Implies" -> Just (Implies antecedent consequent)
                       "Equivalent" -> Just (Equivalent antecedent consequent)


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
equiv a b = (Equivalent a b)

makeAtom :: String -> Formula
makeAtom string = AtomicFormula string

---- Predicates

atomicFormulaP :: Formula -> Bool
atomicFormulaP (AtomicFormula _) = True
atomicFormulaP _ = False

nonAtomicFormulaP :: Formula -> Bool
nonAtomicFormulaP = not . atomicFormulaP

implicationP :: Formula -> Bool
implicationP (Implies _ _) = True
implicationP _ = False

equivalenceP :: Formula -> Bool
equivalenceP (Equivalent _ _) = True
equivalenceP _ = False

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

getAtomicsInFormula :: Formula -> [Formula]
getAtomicsInFormula form@(AtomicFormula string) = [form]
getAtomicsInFormula (Not  form) = getAtomicsInFormula form
getAtomicsInFormula (And forms) = mapAppend getAtomicsInFormula forms
getAtomicsInFormula (Or  forms) = mapAppend  getAtomicsInFormula forms
getAtomicsInFormula (Implies ant cons) =
  getAtomicsInFormula ant ++ getAtomicsInFormula  cons
getAtomicsInFormula (Equivalent one  two) =
  getAtomicsInFormula one ++ getAtomicsInFormula two
getAtomicsInFormula (Necessarily form) = getAtomicsInFormula form
getAtomicsInFormula (Possibly form) = getAtomicsInFormula form

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
