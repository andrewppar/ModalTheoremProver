module Canonicalizer
    (canonicalizeFormula
     , formulaSetsEqualP
     , formulaListsOverlapP) where
import Data.Char
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

---Use this to turn setIntersection from N^2 generally to N Log N generally.
sortFormulas :: [Formula] -> [Formula]
sortFormulas = quickSort formulaLessThanOrEqual

formulaLessThanOrEqual :: Formula -> Formula -> Bool
formulaLessThanOrEqual formulaOne formulaTwo =
    formulaOne == formulaTwo || formulaLessThan formulaOne formulaTwo

formulaLessThan :: Formula -> Formula -> Bool
formulaLessThan formulaOne formulaTwo =
    let rankOne = formulaRank formulaOne
        rankTwo = formulaRank formulaTwo
     in if rankOne < rankTwo
        then True
        else if rankOne == rankTwo
             then complexFormulaLessThan formulaOne formulaTwo
             else False

complexFormulaLessThan :: Formula -> Formula -> Bool
complexFormulaLessThan (AtomicFormula atomOne) (AtomicFormula atomTwo) =
    stringLessThan atomOne atomTwo
complexFormulaLessThan (AtomicFormula atom) _ = True
complexFormulaLessThan (Not negatum1) (Not negatum2) = complexFormulaLessThan negatum1 negatum2
complexFormulaLessThan (Not negatum1) _ = True

complexFormulaLessThan (Implies ant1 con1) (Implies ant2 con2) = complexFormulaLessThan ant1 ant2
complexFormulaLessThan (Implies ant con) (Not negatum) = False
complexFormulaLessThan (Implies ant con) _ = True

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

compareListsByFunction :: (a -> a -> Bool) -> [a] -> [a] -> Bool
compareListsByFunction f [] _ = True
compareListsByFunction f (x:xs) [] = False
compareListsByFunction f (x:xs) (y:ys) = f x y

formulaRank :: Formula -> Int
formulaRank (Not negatum)      = 1 + (formulaRank negatum)
formulaRank (Implies ant cons) = (formulaRank ant) + (formulaRank cons)
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
