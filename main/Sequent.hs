module Sequent
 (Sequent (..)
 , Polarity (..)
 , makePositiveSequent
 , atomicSequentP
 , nonAtomicSequentP
 , gatherFormulas
 , gatherNegations
 , makeSequent 
 , addFormulasToSequent
 , addJuncts
 , emptySequent
 , makeAtomicSequentFromSequent
 , addFormulaToSequentWithPolarity
 , makeNegativeSequent
 , sequentAtomicFormulasByPolarity
 , purelyModalOrAtomicSequentP
 , gatherImplications
 , gatherConjunctions
 , gatherDisjunctions
 , gatherPossibilities
 , sequentRemoveDuplicates 
 , gatherNecessities)
where

import Utilities
import Formula
import Canonicalizer

----------------
--- Sequents ---
----------------
data Sequent = Sequent {negFormulas :: [Formula],
                        posFormulas :: [Formula]}

instance Eq Sequent where
    (Sequent negOne posOne) == (Sequent negTwo posTwo) =
                                    formulaSetsEqualP negOne negTwo &&
                                    formulaSetsEqualP posOne posTwo

instance Show Sequent where
    show sequent = "(" ++ (joinStrings ", " . map show . negFormulas) sequent ++ " ==> " ++ (joinStrings ", " . map show . posFormulas) sequent ++ ")"


data Polarity = Positive | Negative deriving (Eq)

oppositePolarity :: Polarity -> Polarity
oppositePolarity Positive = Negative
oppositePolarity Negative = Positive

makeSequent :: [Formula] -> [Formula] -> Sequent
makeSequent negFormulas posFormulas = Sequent negFormulas posFormulas

emptySequent :: Sequent
emptySequent = makeSequent [] []

addFormulasToSequent :: Polarity -> [Formula] -> Sequent -> Sequent
addFormulasToSequent polarity forms (Sequent negs poss) = 
  case polarity of 
    Positive -> Sequent negs (poss ++ forms)
    Negative -> Sequent (negs ++ forms) poss

getSequentFormulasByPolarity :: Polarity -> Sequent -> [Formula]
getSequentFormulasByPolarity Positive = posFormulas
getSequentFormulasByPolarity Negative = negFormulas

makeSequentByPolarity :: Polarity -> [Formula] -> [Formula] -> Sequent
makeSequentByPolarity Positive formulasMatchingPolarity formulasNotMatchingPolarity =
    makeSequent formulasNotMatchingPolarity formulasMatchingPolarity
makeSequentByPolarity Negative formulasMatchingPolarity formulasNotMatchingPolarity =
    makeSequent formulasMatchingPolarity formulasNotMatchingPolarity

makePositiveSequent :: Formula -> Sequent
makePositiveSequent form = makeSequent [] [form]

makeNegativeSequent :: Formula -> Sequent
makeNegativeSequent form = makeSequent [form] []


recursivelyAddConjunctions :: [Formula] -> [[Formula]] -> [[Formula]]
recursivelyAddConjunctions [] formulaLists  = formulaLists
recursivelyAddConjunctions (formula:formulas) formulaLists = let newFormulaLists = recursivelyAddConjunctions formulas formulaLists
                                                             in if conjunctionP formula
                                                                then generateNewJuncts (conjuncts formula) newFormulaLists
                                                                else addJunctToEachFormulaList formula newFormulaLists

generateNewJuncts :: [Formula] -> [[Formula]] -> [[Formula]]
generateNewJuncts juncts formulaLists = mapAppend (\junct -> (addJunctToEachFormulaList junct formulaLists)) juncts

addJunctToEachFormulaList :: Formula -> [[Formula]] -> [[Formula]]
addJunctToEachFormulaList junct formulaLists = map (\formulaList -> junct : formulaList) formulaLists

separateNegations :: [Formula] -> ([Formula], [Formula])
separateNegations = separateFormulasByType negationP

separatePossibilityFormulas :: [Formula] -> ([Formula], [Formula])
separatePossibilityFormulas = separateFormulasByType possibilityP

separateNecessityFormulas :: [Formula] -> ([Formula], [Formula])
separateNecessityFormulas = separateFormulasByType necessityP

separateFormulasByType :: (Formula -> Bool) -> [Formula] -> ([Formula],[Formula])
separateFormulasByType f formulas = foldr (\formula (acc1, acc2) -> if f formula then ((formula:acc1), acc2) else (acc1, (formula:acc2))) ([],[]) formulas


nonAtomicSequentP :: Sequent -> Bool
nonAtomicSequentP (Sequent negFormulas posFormulas) = hasAtomsP negFormulas || hasAtomsP posFormulas
                                                 where hasAtomsP = anyInListMeetsCriteria nonAtomicFormulaP

atomicSequentP :: Sequent -> Bool
atomicSequentP = not . nonAtomicSequentP

makeAtomicSequentFromSequent :: Sequent -> Sequent
makeAtomicSequentFromSequent sequent =
    (makeSequent (filter atomicFormulaP (negFormulas sequent))
                 (filter atomicFormulaP (posFormulas sequent)))

gatherImplications :: [Formula] -> ([Formula], [Formula])
gatherImplications = gatherFormulas implicationP

gatherConjunctions :: [Formula] -> ([Formula],[Formula])
gatherConjunctions = gatherFormulas conjunctionP

gatherDisjunctions :: [Formula] -> ([Formula],[Formula])
gatherDisjunctions = gatherFormulas disjunctionP

gatherNegations :: [Formula] -> ([Formula],[Formula])
gatherNegations = gatherFormulas negationP

gatherPossibilities :: [Formula] -> ([Formula], [Formula])
gatherPossibilities = gatherFormulas possibilityP

gatherNecessities :: [Formula] -> ([Formula], [Formula])
gatherNecessities = gatherFormulas necessityP

gatherFormulas :: (Formula -> Bool) -> [Formula] -> ([Formula],[Formula])
gatherFormulas predicate formulas =
    foldl
    (\(relevantFormulas, irrelevantFormulas) formula ->
         if predicate formula
         then ((formula:relevantFormulas), irrelevantFormulas)
         else (relevantFormulas, (formula:irrelevantFormulas))
              ) ([],[]) formulas

addJuncts :: Polarity -> (Formula -> [Formula]) -> [Formula] -> Sequent -> [Sequent]
addJuncts _ _ [] sequent = [sequent]
addJuncts polarity gatherFunction (junction:junctions) sequent =
    let recursiveCase = addJuncts polarity gatherFunction junctions sequent
        subformulas   = gatherFunction junction
    in  foldl (\acc sequent ->
                   (map
                    (\formula ->
                         addFormulaToSequentWithPolarity polarity formula sequent) subformulas)
                   ++ acc) [] recursiveCase


-- addPositiveFormulasToSequentAsNewSequent :: [Formula] -> Sequent -> [Sequent]
-- addPositiveFormulasToSequentAsNewSequent formulas sequent =
--     map (\formula -> addPositiveFormulaToSequent formula sequent) formulas

-- addPositiveFormulaToSequent :: Formula -> Sequent -> Sequent
-- addPositiveFormulaToSequent = addFormulaToSequentWithPolarity Positive

-- addNegativeFormulaToSequent :: Formula -> Sequent -> Sequent
-- addNegativeFormulaToSequent = addFormulaToSequentWithPolarity Negative

addFormulaToSequentWithPolarity :: Polarity -> Formula -> Sequent -> Sequent
addFormulaToSequentWithPolarity polarity formula sequent =
    let positiveFormulas = if polarity == Positive
                           then formula:(posFormulas sequent)
                           else posFormulas sequent
        negativeFormulas = if polarity == Negative
                           then formula:(negFormulas sequent)
                           else negFormulas sequent
    in makeSequent negativeFormulas positiveFormulas

sequentAtomicFormulasByPolarity :: Sequent -> Polarity -> [Formula]
sequentAtomicFormulasByPolarity sequent polarity =
    let filterFunction = filter atomicFormulaP
    in case polarity of
         Positive -> filterFunction . posFormulas $ sequent
         Negative -> filterFunction . negFormulas $ sequent

purelyModalOrAtomicSequentP :: Sequent -> Bool
purelyModalOrAtomicSequentP (Sequent negForms posForms) =
    everyInListMeetsCriteria
    (\formula -> atomicFormulaP formula || atomicNecessityP formula) negForms
 && everyInListMeetsCriteria
        (\formula -> atomicFormulaP formula || atomicPossibilityP formula) posForms 

sequentRemoveDuplicates :: Sequent -> Sequent 
sequentRemoveDuplicates (Sequent negs poss) = 
  let newNegs = removeDuplicates . sortFormulas $ negs
      newPoss = removeDuplicates . sortFormulas $ poss
   in Sequent newNegs newPoss
