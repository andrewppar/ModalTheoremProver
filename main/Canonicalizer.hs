module Canonicalizer
    (canonicalizeFormula
     , formulaSetsEqualP
     , formulaListsOverlapP) where
import Debug.Trace
import Utilities
import Formula


{-| Canonicalizer |-}

---------------------
--- Canonicalizer ---
---------------------

canonicalizeFormula :: Formula -> Formula -- Convert a formula to DNF, then if we want to get real fancy we can write heuristics for which disjunct to try first.
canonicalizeFormula formula =
    reorderSubFormulas . reduceNegations . negationIn . modalsIn . implicationOut $ formula

implicationOut :: Formula -> Formula
implicationOut (And conjuncts)                 = (And (map implicationOut conjuncts))
implicationOut (Or disjuncts)                  = (Or  (map implicationOut disjuncts))
implicationOut (Implies antecedent consequent) = (Or [(Not (implicationOut antecedent)), (implicationOut consequent)])
implicationOut (Not negatum)                   = (Not (implicationOut negatum))
implicationOut (Possibly possibility)          = (Possibly (implicationOut possibility))
implicationOut (Necessarily necessity)         = (Necessarily (implicationOut necessity))
implicationOut atomic                          = atomic

negationIn :: Formula -> Formula
negationIn (And conjuncts)                  = (And (map negationIn conjuncts))
negationIn (Or disjuncts)                   = (Or  (map negationIn disjuncts))
negationIn (Implies antecedent consequent) =
    (Implies (negationIn antecedent) (negationIn consequent))
negationIn (Not (And (conjuncts))) = (Or (map (\formula -> (negationIn (Not formula))) conjuncts))
negationIn (Not (Or  (disjuncts))) = (And (map (\formula -> (negationIn (Not formula))) disjuncts))
negationIn (Not (Not negatum)) = (Not (Not (negationIn negatum)))
negationIn (Not (Implies antecedent consequent)) = (And [(negationIn antecedent),
                                                        (negationIn (Not consequent))])
negationIn (Not (Possibly possibility))  = (Necessarily (negationIn (Not possibility)))
negationIn (Not (Necessarily necessity)) = (Possibly (negationIn (Not necessity)))
negationIn (Possibly possibility) = (Possibly (negationIn possibility))
negationIn (Necessarily necessity) = (Necessarily (negationIn necessity))
negationIn atomic = atomic

reduceNegations :: Formula -> Formula  -- remove any double negations
reduceNegations (And conjuncts) = (And (map reduceNegations conjuncts))
reduceNegations (Or disjuncts)  = (Or  (map reduceNegations disjuncts))
reduceNegations (Implies antecedent consequent) = (Implies (reduceNegations antecedent) (reduceNegations consequent))
reduceNegations (Not (Not negatum)) = (reduceNegations negatum)
reduceNegations (Not (Possibly possibility)) = (Necessarily (Not possibility))
reduceNegations (Not (Necessarily necessity)) = (Possibly (Not necessity))
reduceNegations (Not negatum) = (Not (reduceNegations negatum))
reduceNegations (Possibly possibility) = (Possibly (reduceNegations possibility))
reduceNegations (Necessarily necessity) = (Necessarily (reduceNegations necessity))
reduceNegations atom = atom

modalsIn :: Formula -> Formula
modalsIn (Not negatum) = (Not (modalsIn negatum))
modalsIn (And conjuncts) = (And  (map modalsIn conjuncts))
modalsIn (Or disjuncts) = (Or (map modalsIn disjuncts))
modalsIn (Implies antecedent consequent) = (Implies (modalsIn antecedent) (modalsIn consequent))
modalsIn (Possibly (Not negatum)) = (Not (Necessarily (modalsIn negatum)))
modalsIn (Possibly (Or disjuncts)) = (Or (map (Possibly . modalsIn) disjuncts))
modalsIn (Possibly (And conjuncts)) = (Possibly (And (map modalsIn  conjuncts)))
modalsIn (Possibly (Implies antecedent consequent)) =
    (Possibly (Implies (modalsIn antecedent) (modalsIn consequent)))
modalsIn (Necessarily (Not negatum)) = (Not (Possibly (modalsIn negatum)))
modalsIn (Necessarily (Or disjuncts)) = (Necessarily (Or (map modalsIn disjuncts)))
modalsIn (Necessarily (And conjuncts)) = (And (map Necessarily conjuncts))
modalsIn (Necessarily (Implies antecedent consequent)) =
    (Necessarily (Implies (modalsIn antecedent) (modalsIn consequent)))
modalsIn atom = atom

reorderSubFormulas :: Formula -> Formula
reorderSubFormulas (Not negatum) = (Not (reorderSubFormulas negatum))
reorderSubFormulas (Implies antecedent consequent) =
    (Implies (reorderSubFormulas antecedent) (reorderSubFormulas consequent))
reorderSubFormulas (And conjuncts) =
    let newConjuncts = (map reorderSubFormulas) . removeDuplicates . sortFormulas $ conjuncts
    in if (length newConjuncts) == 1
       then (head newConjuncts)
       else (And newConjuncts)
reorderSubFormulas (Or disjuncts) =
    let newDisjuncts = (map reorderSubFormulas) . removeDuplicates . sortFormulas $ disjuncts
    in if (length newDisjuncts) == 1
       then (head newDisjuncts)
       else (Or newDisjuncts)
reorderSubFormulas (Necessarily necessity) = (Necessarily (reorderSubFormulas necessity))
reorderSubFormulas (Possibly possibility) = (Possibly (reorderSubFormulas possibility))
reorderSubFormulas atom = atom


--------------------------------------
--- Canonical Ordering Of Formulas ---
--------------------------------------


formulaTransform :: Formula -> (Formula -> Formula) -> Formula
formulaTransform (Not negatum) f = Not . f $ negatum
formulaTransform (Implies ant cons) f = Implies (f ant) (f cons)
formulaTransform (And conjuncts) f = And . (map f) $ conjuncts
formulaTransform (Or disjuncts) f = Or . (map f) $ disjuncts
formulaTransform atom f = f atom

formulaSetsEqualP :: [Formula] -> [Formula] -> Bool
formulaSetsEqualP formsOne formsTwo =
    let sortedOne = removeDuplicates . sortFormulas $ formsOne
        sortedTwo = removeDuplicates . sortFormulas $ formsTwo
    in sortedOne == sortedTwo

formulaListsOverlapP :: [Formula] -> [Formula] -> Bool
formulaListsOverlapP formulasOne formulasTwo  = listsOverlapP formulaLessThan formulasOne formulasTwo
