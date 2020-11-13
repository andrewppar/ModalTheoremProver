module ModalTheoremProver.Canonicalizer
    (canonicalizeFormula
     , formulaSetsEqualP
     , formulaListsOverlapP) where
import Debug.Trace
import ModalTheoremProver.Utilities
import ModalTheoremProver.Formula


{-| Canonicalizer |-}

---------------------
--- Canonicalizer ---
---------------------

canonicalizeFormula :: Formula -> Formula -- Convert a formula to DNF, then if we want to get real fancy we can write heuristics for which disjunct to try first.
canonicalizeFormula formula =
    reorderSubFormulas
  . reduceModals
  . modalsOut
  . reduceNegations
  . negationIn
  . implicationOut
  . simplifyEquivalence $ formula

implicationOut :: Formula -> Formula
implicationOut (And conjuncts)                 =
  (And (map implicationOut conjuncts))
implicationOut (Or disjuncts)                  =
  (Or  (map implicationOut disjuncts))
implicationOut (Implies antecedent consequent) =
  (Or [(Not (implicationOut antecedent)), (implicationOut consequent)])
implicationOut (Equivalent one two)            =
  (Equivalent (implicationOut one) (implicationOut two))
implicationOut (Not negatum)                   =
  (Not (implicationOut negatum))
implicationOut (Possibly possibility)          =
  (Possibly (implicationOut possibility))
implicationOut (Necessarily necessity)         =
  (Necessarily (implicationOut necessity))
implicationOut atomic                          =
  atomic

negationIn :: Formula -> Formula
negationIn (And conjuncts)                  =
  (And (map negationIn conjuncts))
negationIn (Or disjuncts)                   =
  (Or  (map negationIn disjuncts))
negationIn (Implies antecedent consequent) =
    (Implies (negationIn antecedent) (negationIn consequent))
negationIn (Equivalent one two) =
  (Equivalent (negationIn one) (negationIn two))
negationIn (Not (And (conjuncts))) =
  (Or (map (\formula -> (negationIn (Not formula))) conjuncts))
negationIn (Not (Or  (disjuncts))) =
  (And (map (\formula -> (negationIn (Not formula))) disjuncts))
negationIn (Not (Not negatum)) =
  (Not (Not (negationIn negatum)))
negationIn (Not (Implies antecedent consequent)) =
  (And [(negationIn antecedent), (negationIn (Not consequent))])
negationIn (Not (Equivalent one two)) =
  (Equivalent (Not one) two)
negationIn (Not (Possibly possibility))  =
  (Necessarily (negationIn (Not possibility)))
negationIn (Not (Necessarily necessity)) =
  (Possibly (negationIn (Not necessity)))
negationIn (Possibly possibility) =
  (Possibly (negationIn possibility))
negationIn (Necessarily necessity) =
  (Necessarily (negationIn necessity))
negationIn atomic = atomic

reduceNegations :: Formula -> Formula  -- remove any double negations
reduceNegations (And conjuncts) = (And (map reduceNegations conjuncts))
reduceNegations (Or disjuncts)  = (Or  (map reduceNegations disjuncts))
reduceNegations (Implies antecedent consequent) =
  (Implies (reduceNegations antecedent) (reduceNegations consequent))
reduceNegations (Equivalent one two) =
  (Equivalent (reduceNegations one) (reduceNegations two))
reduceNegations (Not (Not negatum)) = (reduceNegations negatum)
reduceNegations (Not (Possibly possibility)) = (Necessarily (Not possibility))
reduceNegations (Not (Necessarily necessity)) = (Possibly (Not necessity))
reduceNegations (Not negatum) = (Not (reduceNegations negatum))
reduceNegations (Possibly possibility) = (Possibly (reduceNegations possibility))
reduceNegations (Necessarily necessity) =
  (Necessarily (reduceNegations necessity))
reduceNegations atom = atom

modalsIn :: Formula -> Formula
modalsIn (Not negatum) = (Not (modalsIn negatum))
modalsIn (And conjuncts) = (And  (map modalsIn conjuncts))
modalsIn (Or disjuncts) = (Or (map modalsIn disjuncts))
modalsIn (Implies antecedent consequent) = (Implies (modalsIn antecedent) (modalsIn consequent))
modalsIn (Equivalent one two) = (Equivalent (modalsIn one) (modalsIn two))
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

modalsOut :: Formula -> Formula
modalsOut form@(AtomicFormula _) = form
modalsOut (Not negatum) = Not . modalsOut $ negatum
modalsOut form@(And conjuncts) =
  if all necessityP conjuncts
     then (Necessarily (And (map (necessity . modalsOut) conjuncts)))
     else form
modalsOut form@(Or disjuncts) =
    if all possibilityP disjuncts
       then (Possibly (Or (map (possibility . modalsOut) disjuncts)))
       else form
modalsOut (Implies antecedent consequent) =
    (Implies (modalsOut antecedent) (modalsOut consequent))
modalsOut (Equivalent one two) =
    (Equivalent (modalsOut one) (modalsOut two))
modalsOut (Possibly possibility) = Possibly . modalsOut $ possibility
modalsOut (Necessarily necessity) = Necessarily . modalsOut $ necessity

reduceModals :: Formula -> Formula
reduceModals form@(AtomicFormula _) = form
reduceModals (Not negatum) = Not . reduceModals $ negatum
reduceModals (And conjuncts) = And . map reduceModals $ conjuncts
reduceModals (Or disjuncts) = Or . map reduceModals $ disjuncts
reduceModals (Implies antecedent consequent) =
    (Implies (reduceModals antecedent) (reduceModals consequent))
reduceModals (Equivalent one two) =
    (Equivalent (reduceModals one) (reduceModals two))
reduceModals (Possibly (Possibly possibility)) =
    Possibly . reduceModals $ possibility
reduceModals (Possibly possibility) = Possibly . reduceModals $ possibility
reduceModals (Necessarily (Necessarily necessity)) =
    Necessarily . reduceModals $ necessity
reduceModals (Necessarily necessity) = Necessarily . reduceModals $ necessity



simplifyEquivalence :: Formula -> Formula
simplifyEquivalence form@(AtomicFormula _) = form
simplifyEquivalence (Not negatum) = Not . simplifyEquivalence $ negatum
simplifyEquivalence (And conjuncts) = And . map simplifyEquivalence $ conjuncts
simplifyEquivalence (Or disjuncts) = Or . map simplifyEquivalence $ disjuncts
simplifyEquivalence (Implies antecedent consequent) =
  if antecedent == consequent
     then  Implies (AtomicFormula "p") (AtomicFormula "p")
     else Implies (simplifyEquivalence antecedent) (simplifyEquivalence consequent)
simplifyEquivalence (Necessarily necessity) =
  Necessarily . simplifyEquivalence $ necessity
simplifyEquivalence (Possibly possibility) =
  Possibly . simplifyEquivalence $ possibility
simplifyEquivalence (Equivalent one two) =
  if one == two
     then Implies (AtomicFormula "p") (AtomicFormula "p") -- TODO conisder introducing Top and bot to take one more step off of proofs.
     else let simpleOne = simplifyEquivalence one
              simpleTwo = simplifyEquivalence two
           in (And [ (Implies simpleOne simpleTwo)
                   , (Implies simpleTwo simpleOne)])


reorderSubFormulas :: Formula -> Formula
reorderSubFormulas (Not negatum) = (Not (reorderSubFormulas negatum))
reorderSubFormulas (Implies antecedent consequent) =
    (Implies (reorderSubFormulas antecedent) (reorderSubFormulas consequent))
reorderSubFormulas form@(Equivalent one two) =
  if formulaLessThan one two
     then form
     else (Equivalent two  one)
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
formulaTransform (Equivalent one two) f = Equivalent (f one) (f two)
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
