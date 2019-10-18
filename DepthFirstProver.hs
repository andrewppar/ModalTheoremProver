module DepthFirstProver
    (PropProofTree (..)
    , Tree (..)
    , ProofTreeStatus (..)
    , propositionalProve
    , proveK
    , proveT
    , prove4

    -- For Testsing
    , classicalLeftNegation
    , classicalLeftConjunction
    , classicalLeftDisjunction
    , classicalRightConjunction
    , proofStatusSum
    , contractRootNode
    , contractLevel1Nodes
    , contractLevelNNodes
    , weakenLevel1Nodes
    , weakenLevelNNodes
    ) where

import Control.Parallel
import Control.Parallel.Strategies
import Data.Char
import Debug.Trace
import Utilities
import Formula
import Canonicalizer
import Sequent
import Hypersequent

--import Testing

-- @todo We need a way of sorting hypersequents so that we can have a fast way of removing duplicates list.

---------------------------
--- The ProofTree Class ---
---------------------------

data Tree a = Close | Leaf | Node a [Tree a]
            deriving (Eq)

instance (Show a) => Show (Tree a) where
    show tree = showTree tree 0

showTree :: (Show a) => (Tree a) -> Int -> String
showTree Leaf depth = (replicate depth ' ') ++ "O\n"
showTree Close depth = (replicate depth ' ') ++ "X\n"
showTree (Node a trees) depth =
    (replicate depth ' ') ++ "-" ++ (show a ) ++ "\n" ++
                              (joinStrings " " (map (\tree -> showTree tree (5+ depth)) trees))

showTrees :: [ModalProofTree] -> String
showTrees [] = "\n"
showTrees (x:xs) = show x ++ "\n" ++ showTrees xs

class ProofTree a where
    axiomP                 :: a -> Bool
    gatherLeafNodes     :: Tree a -> [a]

    gatherLeafNodes Leaf = []
    gatherLeafNodes Close = []
    gatherLeafNodes (Node seq [Leaf]) = [seq]
    gatherLeafNodes (Node seq [Close]) = [seq]
    gatherLeafNodes (Node seq trees) = mapAppend gatherLeafNodes trees


data ProofTreeStatus = Proven | NotProven | CounterExampleGenerated | Continue deriving (Show,Eq)

{-| Propositional Theorem Prover |-}
-- We want to do depth first proofs and we want to ensure that we can use hypersequents. The thought here is that we'll be able to take advantage of parallel algorithms better if we've got depth first proof search and we're using hypersequents.

instance ProofTree Sequent where
    axiomP sequent = not . emptyListP . setIntersection (posFormulas sequent) . negFormulas $ sequent


type PropProofTree = Tree Sequent

maxProofDepth :: Int
maxProofDepth = 5

propositionalProve :: Formula -> Bool
propositionalProve formula =
    let canonForm = canonicalizeFormula formula
        (prooftree, status) = generatePropositionalProofTreeFromFormula canonForm
    in  if status == Proven
        then True
        else False

generatePropositionalProofTreeFromFormula :: Formula -> (PropProofTree, ProofTreeStatus)
generatePropositionalProofTreeFromFormula formula =
    let startingSequent = makePositiveSequent formula
        startingTree    = generatePropositionalStartingTree startingSequent
        finishedTree    = generatePropositionalProofTree startingTree 0
        status          = getPropProofTreeStatus finishedTree -- @todo wrap this inside generatePropositionalProofTree for efficiency, no need to walk the tree twice.
    in (finishedTree, status)


generatePropositionalStartingTree :: Sequent -> PropProofTree
generatePropositionalStartingTree sequent = Node sequent [Leaf]

generatePropositionalProofTree :: PropProofTree -> Int -> PropProofTree
generatePropositionalProofTree Close _ = Close
generatePropositionalProofTree Leaf  _ = Leaf
generatePropositionalProofTree (Node sequent [Leaf]) depth =
    if axiomP sequent
       then Node sequent [Close]
       else if atomicSequentP sequent || depth >= maxProofDepth
            then Node sequent [Leaf]
            else let newSequents      = applyRulesOneStep [sequent]
                     newStartingTrees = map generatePropositionalStartingTree newSequents
                 in  Node sequent ((parMap rseq)
                                   (\tree -> generatePropositionalProofTree tree (1+ depth))
                                   newStartingTrees)
generatePropositionalProofTree (Node sequent trees) depth =
    Node sequent (map (\tree -> generatePropositionalProofTree tree depth) trees)

getPropProofTreeStatus :: PropProofTree -> ProofTreeStatus
getPropProofTreeStatus Leaf  = NotProven
getPropProofTreeStatus Close = Proven
getPropProofTreeStatus (Node sequent [Leaf]) =
    if atomicSequentP sequent
    then CounterExampleGenerated
    else NotProven
getPropProofTreeStatus (Node sequent trees) =
    proofStatusSum . map getPropProofTreeStatus $ trees


proofStatusSum :: [ProofTreeStatus] -> ProofTreeStatus
proofStatusSum statuses = foldl (\sum status ->
                                     case status of
                                       Proven -> sum
                                       NotProven -> if sum == CounterExampleGenerated
                                                    then sum
                                                    else NotProven
                                       CounterExampleGenerated -> CounterExampleGenerated)
                          Proven statuses

applyRulesOneStep :: [Sequent] -> [Sequent]
applyRulesOneStep sequents = classicalRightConjunction .
                             classicalLeftDisjunction .
                             classicalRightNegation .
                             classicalLeftNegation .
                             classicalLeftConjunction .
                             classicalRightDisjunction $ sequents



classicalRightConjunction :: [Sequent] -> [Sequent]
classicalRightConjunction = branchingRuleWithPolarityAndType Positive conjunctionP conjuncts

classicalLeftDisjunction :: [Sequent] -> [Sequent]
classicalLeftDisjunction = branchingRuleWithPolarityAndType Negative disjunctionP disjuncts

branchingRuleWithPolarityAndType :: Polarity -> (Formula -> Bool) -> (Formula -> [Formula]) -> [Sequent] -> [Sequent]
branchingRuleWithPolarityAndType polarity predicate gatherFunction sequents =
    foldl (\acc sequent ->
               let positiveFormulas = posFormulas sequent
                   negativeFormulas = negFormulas sequent
                   (relevantFormulas, irrelevantFormulas) =
                       case polarity of
                         Positive -> gatherFormulas predicate positiveFormulas
                         Negative -> gatherFormulas predicate negativeFormulas
                   irrelevantSequent =
                       case polarity of
                         Positive -> makeSequent negativeFormulas irrelevantFormulas
                         Negative -> makeSequent irrelevantFormulas positiveFormulas
                   newSequents =
                       addJuncts polarity gatherFunction relevantFormulas irrelevantSequent
               in newSequents ++ acc) [] sequents

classicalLeftConjunction :: [Sequent] -> [Sequent]
classicalLeftConjunction = nonBranchingRuleWithPolarityAndType Negative conjunctionP conjuncts


classicalRightDisjunction :: [Sequent] -> [Sequent]
classicalRightDisjunction = nonBranchingRuleWithPolarityAndType Positive disjunctionP disjuncts

nonBranchingRuleWithPolarityAndType :: Polarity -> (Formula -> Bool) -> (Formula -> [Formula]) -> [Sequent] -> [Sequent]
nonBranchingRuleWithPolarityAndType polarity predicate gatherFunction sequents =
    map (\sequent ->
             let positiveFormulas = posFormulas sequent
                 negativeFormulas = negFormulas sequent
                 (relevantFormulas, irrelevantFormulas) =
                     case polarity of
                       Positive -> gatherFormulas predicate positiveFormulas
                       Negative -> gatherFormulas predicate negativeFormulas
                 newSubformulas   = mapAppend gatherFunction relevantFormulas
                 newFormulas = irrelevantFormulas ++ newSubformulas
             in case polarity of
                  Positive -> makeSequent negativeFormulas newFormulas
                  Negative -> makeSequent newFormulas positiveFormulas) sequents

classicalRightNegation :: [Sequent] -> [Sequent]
classicalRightNegation = negationRuleByPolarity Positive

classicalLeftNegation :: [Sequent] -> [Sequent]
classicalLeftNegation = negationRuleByPolarity Negative

negationRuleByPolarity :: Polarity -> [Sequent] -> [Sequent]
negationRuleByPolarity polarity sequents =
    map
    (\sequent ->
         let positiveFormulas = posFormulas sequent
             negativeFormulas = negFormulas sequent
             (relevantFormulas, irrelevantFormulas) =
                 case polarity of
                   Positive -> gatherFormulas negationP positiveFormulas
                   Negative -> gatherFormulas negationP negativeFormulas
             newSubformulas = map negatum relevantFormulas
         in case polarity of
              Positive -> makeSequent (negativeFormulas ++ newSubformulas) irrelevantFormulas
              Negative -> makeSequent irrelevantFormulas (positiveFormulas ++ newSubformulas))
    sequents

{-| Modal Logic |-}

data System = K | T | Four

type ModalProofTree = Tree Hypersequent

hypersequentAxiomP :: Hypersequent -> Bool
hypersequentAxiomP BranchEnd = False
hypersequentAxiomP (World sequent hypersequents) =
    if axiomP sequent
    then  True
    else   generalizedDisjunction . (map hypersequentAxiomP) $ hypersequents

gatherModalOpenLeafNodes :: ModalProofTree -> [Hypersequent]
gatherModalOpenLeafNodes Leaf = []
gatherModalOpenLeafNodes Close = []
gatherModalOpenLeafNodes (Node seq [Leaf]) = [seq]
gatherModalOpenLeafNodes (Node seq [Close]) = []
gatherModalOpenLeafNodes (Node seq trees) = mapAppend gatherModalOpenLeafNodes trees



emptyModalProofTree :: ModalProofTree
emptyModalProofTree = (Node emptyHypersequent [Leaf])

modalProofTreesStatus :: [ModalProofTree] -> [ModalProofTree] -> Int -> System -> (ModalProofTree, ProofTreeStatus)
modalProofTreesStatus oldTrees newTrees depth system =
    if oldTrees == newTrees ||
       depth >= maxProofDepth
    then ((head newTrees), NotProven)
    else surveyProofTreesForStatus newTrees system

surveyProofTreesForStatus :: [ModalProofTree] -> System -> (ModalProofTree, ProofTreeStatus)
surveyProofTreesForStatus [] _ = (emptyModalProofTree, Continue)
surveyProofTreesForStatus (tree:trees) system =
    let status = getModalProofTreeStatus tree system
    in  case status of
          Proven -> (tree, status)
          CounterExampleGenerated ->
              let nextPossibleReturn@(possiblyNewExemplar, possiblyNewStatus) =
                      surveyProofTreesForStatus trees system
              in if possiblyNewStatus == Proven
                 then nextPossibleReturn
                 else (tree, status)
          NotProven -> surveyProofTreesForStatus trees system

getModalProofTreeStatus :: ModalProofTree -> System -> ProofTreeStatus
getModalProofTreeStatus tree system =
    let openLeafNodes = (gatherModalOpenLeafNodes tree)
    in
      if openLeafNodes == []
       then Proven
       else if leafNodesContainModalCounterExampleP openLeafNodes system
            then CounterExampleGenerated
            else NotProven

leafNodesContainModalCounterExampleP :: [Hypersequent] -> System -> Bool
leafNodesContainModalCounterExampleP hypersequents system =
    let potentialCounterExamples =
            filter purelyModalOrAtomicHypersequentP hypersequents -- with only ATOMIC modals, i.e. modal formulas that have an atomic formula as a subformula
    in case system of
--      K -> kCounterExampleInListP potentialCounterExamples
      T -> tCounterExampleInListP potentialCounterExamples
      Four -> fourCounterExampleInListP potentialCounterExamples
      otherwise -> kCounterExampleInListP potentialCounterExamples

--- CounterExamples For A System ---

-- @todo abstract out the common internals for all of these and make the above function just call those.

kCounterExampleInListP :: [Hypersequent] -> Bool
kCounterExampleInListP = anyInListMeetsCriteria kCounterExampleP

kCounterExampleP :: Hypersequent -> Bool
-- At this point we know that all we have are modal statements. So as long as there is no world such that there is a left box or right diamond with the corresponding unmodalized formula in a connected world. @todo leave the modal stuff around
kCounterExampleP BranchEnd = True
kCounterExampleP (World sequent hypersequents) =
    let negativeNecessities     = map necessity . filter necessityP . negFormulas $ sequent
        positivePossibilities   = map possibility . filter possibilityP . posFormulas $ sequent
        negativeSuccessorAtoms  = getSuccessors Negative
        positiveSuccessorsAtoms = getSuccessors Positive
    in if formulaListsOverlapP negativeNecessities negativeSuccessorAtoms ||
       formulaListsOverlapP positivePossibilities positiveSuccessorsAtoms
       then False
       else generalizedConjunction . map kCounterExampleP $ hypersequents
            where getSuccessors polarity =
                      mapAppend (\hypersequent ->
                               hypersequentBaseAtomicFormulas hypersequent polarity)
                      hypersequents

tCounterExampleInListP :: [Hypersequent] -> Bool
tCounterExampleInListP = anyInListMeetsCriteria tCounterExampleP

fourCounterExampleInListP :: [Hypersequent] -> Bool
fourCounterExampleInListP = anyInListMeetsCriteria fourCounterExampleP

tCounterExampleP :: Hypersequent -> Bool
tCounterExampleP BranchEnd = True
tCounterExampleP (World sequent hypersequents) =
    let negativeNecessities     = map necessity . filter necessityP . negFormulas $ sequent
        positivePossibilities   = map possibility . filter possibilityP . posFormulas $ sequent
        negativePropositions    = sequentAtomicFormulasByPolarity sequent Negative
        positivePropositions    = sequentAtomicFormulasByPolarity sequent Positive
    in  if formulaListsOverlapP negativePropositions positivePossibilities ||
        formulaListsOverlapP positivePropositions negativeNecessities
        then False
        else generalizedConjunction . map tCounterExampleP $ hypersequents


-- @todo we need to handle literals in the counter-example case, instead of just modalAtoms and we should have a way to say that a failed counterexample really will become a proof.

fourCounterExampleP :: Hypersequent -> Bool
fourCounterExampleP BranchEnd = True
fourCounterExampleP (World sequent hypersequents) =
    let negativeNecessities   = map necessity . filter necessityP . negFormulas $ sequent
        positivePossibilities = map possibility . filter possibilityP . posFormulas $ sequent
        forwardPositiveAtoms  = mapAppend (gatherAtomicSentencesByPolarity Positive) hypersequents
        forwardNegativeAtoms  = mapAppend (gatherAtomicSentencesByPolarity Negative) hypersequents
    in if formulaListsOverlapP negativeNecessities forwardPositiveAtoms ||
        formulaListsOverlapP positivePossibilities forwardNegativeAtoms
       then False
       else generalizedConjunction . map fourCounterExampleP $ hypersequents




-- fourCounterExampleP :: [HyperSequent] -> Bool
-- fourCounterExampleP hypersequents =
--     if (filter closableInFour hypersequents) == []
--        then True
--       else False

--closableInFour :: Hypersequent -> Bool
--closableInFour hypersequent = -- what could we possibly put here to distinguish between (p => [] p) and ([] p => [] [] p). They will at some point end up with the same ground hypersequents. -- counterexample checking can be a fast fail in K and hard coded elsewhere, but we can't provide general algorightms for counterexample checks -- I feel like this has been proved somewhere.

groundHypersequentP :: Hypersequent -> Bool
groundHypersequentP = everyInHypersequent atomicSequentP

makeGroundHypersequentFromHypersequent :: Hypersequent -> Hypersequent
makeGroundHypersequentFromHypersequent BranchEnd = BranchEnd
makeGroundHypersequentFromHypersequent (World sequent hypersequents) =
    (World (makeAtomicSequentFromSequent sequent)
               (map makeGroundHypersequentFromHypersequent hypersequents))

proveK :: Formula -> Bool
proveK formula = modalProve formula K

proveT :: Formula -> Bool
proveT formula = modalProve formula T

prove4 :: Formula -> Bool
prove4 formula = modalProve formula Four

modalProve :: Formula -> System -> Bool
modalProve formula system =
    let startingHypersequent = makeStartingHypersequent . canonicalizeFormula $ formula
        startingProofTree    = (Node startingHypersequent [Leaf])
        (relevantProofTree, status)
            = generateHypersequentProofTree [startingProofTree] system 0
    in case status of
         Proven -> True
         otherwise -> False

generateHypersequentProofTree :: [ModalProofTree] -> System -> Int -> (ModalProofTree, ProofTreeStatus)
-- We use lists of hypersequents because there are many ways of applying structural rules and we want to try them all.
generateHypersequentProofTree proofTrees system depth =
    let newProofTrees = modalProveOneStep proofTrees system
        (relevantTree, status) = modalProofTreesStatus proofTrees newProofTrees depth system
    in case status of
       Proven  -> (relevantTree, status)
       CounterExampleGenerated -> (relevantTree, status)
       NotProven -> (relevantTree, status)
       Continue ->  generateHypersequentProofTree newProofTrees system (depth + 1)


modalProveOneStep :: [ModalProofTree] -> System -> [ModalProofTree]
modalProveOneStep trees system =  (map applyInnerRules) .
                                  (map applyLeftNecessity) .
                                  (map applyRightPossibility) .
                                  slowRemoveDuplicates .
                                  applyStructuralRules system .
                                  (map applyInnerRules) $ trees

applyInnerRules :: ModalProofTree -> ModalProofTree
applyInnerRules = applyInnerRulesToQuiescnece


applyInnerRulesToQuiescnece :: ModalProofTree -> ModalProofTree
applyInnerRulesToQuiescnece proofTree =
    let newTree = applyInnerRulesOneStep proofTree
    in if newTree == proofTree
       then newTree
       else applyInnerRulesToQuiescnece newTree

applyInnerRulesOneStep :: ModalProofTree -> ModalProofTree
applyInnerRulesOneStep = applyLeftPossibility .
                  applyRightNecessity .
                  applyPropositionalRulesToQuiescence

applyPropositionalRulesToQuiescence :: ModalProofTree -> ModalProofTree
applyPropositionalRulesToQuiescence proofTree =
   let newTree =  (applyPropositionalRule hypersequentLeftConjunction) .
                  (applyPropositionalRule hypersequentRightDisjunction) .
                  (applyPropositionalRule hypersequentLeftNegation) .
                  (applyPropositionalRule hypersequentRightNegtaion) .
                  (applyPropositionalRule hypersequentRightConjunction) .
                  (applyPropositionalRule hypersequentLeftDisjunction) $ proofTree
   in if modalProofTreePropositionalQuiesceDoneP proofTree newTree
      then newTree
      else applyPropositionalRulesToQuiescence newTree

modalProofTreePropositionalQuiesceDoneP :: ModalProofTree -> ModalProofTree -> Bool
modalProofTreePropositionalQuiesceDoneP oldTree newTree =
    if oldTree == newTree || [] == (gatherModalOpenLeafNodes newTree)
    then True
    else False

applyPropositionalRule :: (Hypersequent -> [Hypersequent]) -> ModalProofTree -> ModalProofTree
applypropositionalrule _ Leaf = Leaf
applyPropositionalRule _ Close = Close
applyPropositionalRule hypersequentTransform (Node hypersequent [Leaf]) =
    let newHypersequents = hypersequentTransform hypersequent
        nullCaseP        = [hypersequent] == newHypersequents
    in if nullCaseP
       then (Node hypersequent [Leaf])
       else extendProofTreePossiblyClosingBranches hypersequent newHypersequents
applyPropositionalRule hypersequentTransform (Node hypersequent trees) =
    Node hypersequent (map (applyPropositionalRule hypersequentTransform) trees)

extendProofTreePossiblyClosingBranches :: Hypersequent -> [Hypersequent] -> ModalProofTree
extendProofTreePossiblyClosingBranches hypersequent newHypersequents =
    (Node hypersequent (map makeTreePossiblyClosingBranch newHypersequents))

makeTreePossiblyClosingBranch :: Hypersequent -> ModalProofTree
makeTreePossiblyClosingBranch hypersequent =
    (Node hypersequent (if hypersequentAxiomP hypersequent then [Close] else [Leaf]))

-- Propositional Rules

hypersequentLeftConjunction :: Hypersequent -> [Hypersequent]
hypersequentLeftConjunction = applyPropositionalRuleToHypersequent classicalLeftConjunction

hypersequentRightDisjunction :: Hypersequent -> [Hypersequent]
hypersequentRightDisjunction = applyPropositionalRuleToHypersequent classicalRightDisjunction

hypersequentLeftNegation :: Hypersequent -> [Hypersequent]
hypersequentLeftNegation = applyPropositionalRuleToHypersequent classicalLeftNegation

hypersequentRightNegtaion :: Hypersequent -> [Hypersequent]
hypersequentRightNegtaion = applyPropositionalRuleToHypersequent classicalRightNegation

hypersequentLeftDisjunction :: Hypersequent -> [Hypersequent]
hypersequentLeftDisjunction = applyPropositionalRuleToHypersequent classicalLeftDisjunction

hypersequentRightConjunction :: Hypersequent -> [Hypersequent]
hypersequentRightConjunction = applyPropositionalRuleToHypersequent classicalRightConjunction

applyPropositionalRuleToHypersequent :: ([Sequent] -> [Sequent]) -> Hypersequent -> [Hypersequent]
applyPropositionalRuleToHypersequent _ BranchEnd = [BranchEnd]
applyPropositionalRuleToHypersequent sTransform (World sequent hypersequents) =
    let newSequents = sTransform [sequent]
        newHypersequents = cartesianProduct .
                           (map (applyPropositionalRuleToHypersequent sTransform)) $ hypersequents
    in mapAppend (\sequent -> makeNewHypersequent sequent newHypersequents) newSequents

makeNewHypersequent :: Sequent -> [[Hypersequent]] -> [Hypersequent]
makeNewHypersequent sequent hypersequentsList = map (World sequent) hypersequentsList

--Modal Rules
applyLeftNecessity :: ModalProofTree -> ModalProofTree
applyLeftNecessity = applyModalRule hypersequentLeftNecessity

applyRightPossibility :: ModalProofTree -> ModalProofTree
applyRightPossibility = applyModalRule hypersequentRightPossibility

applyRightNecessity :: ModalProofTree -> ModalProofTree
applyRightNecessity = applyModalRule hypersequentRightNecessity

applyLeftPossibility :: ModalProofTree -> ModalProofTree
applyLeftPossibility = applyModalRule hypersequentLeftPossibility

applyModalRule :: (Hypersequent -> Hypersequent) -> ModalProofTree -> ModalProofTree
applyModalRule _ Leaf  = Leaf
applyModalRule _ Close = Close
applyModalRule hypersequentTransform (Node hypersequent [Leaf]) =
    let newHypersequent = hypersequentTransform hypersequent
        nullResult      = newHypersequent == hypersequent
        leafNode        = if hypersequentAxiomP newHypersequent
                          then Close
                          else Leaf
    in if nullResult
       then (Node hypersequent [leafNode])
       else (Node hypersequent [(Node newHypersequent [leafNode])])
applyModalRule  hypersequentTransform (Node hypersequent modalProofTrees) =
    (Node hypersequent (map (applyModalRule hypersequentTransform) modalProofTrees))


hypersequentRightPossibility :: Hypersequent -> Hypersequent
hypersequentRightPossibility = hypersequentUniversalModal Positive possibilityP possibility

hypersequentLeftNecessity :: Hypersequent -> Hypersequent
hypersequentLeftNecessity = hypersequentUniversalModal Negative necessityP necessity

hypersequentUniversalModal :: Polarity -> (Formula -> Bool) -> (Formula -> Formula) -> Hypersequent -> Hypersequent -- @todo experiment here whether structural rules or rules for the application of universalModals per system is more efficent. I think the where we put formulas in the hypersequent will be more efficient.
hypersequentUniversalModal _ _ _ BranchEnd = BranchEnd
hypersequentUniversalModal _ _ _ (World sequent [BranchEnd]) = (World sequent [BranchEnd])
hypersequentUniversalModal polarity test subformula (World sequent hypersequents) =
    let positiveFormulas = posFormulas sequent
        negativeFormulas = negFormulas sequent
        (relevantFormulas, irrelevantFormulas) =
            gatherFormulas test (case polarity of
                                          Positive -> positiveFormulas
                                          Negative -> negativeFormulas)
        atomicModalFormulas = filter atomicModalFormulaP relevantFormulas
        newSequent          =
            case polarity of
              Positive -> makeSequent negativeFormulas (irrelevantFormulas ++ atomicModalFormulas)
              Negative -> makeSequent (irrelevantFormulas ++ atomicModalFormulas) positiveFormulas
        recursiveHypersequents =
            map (hypersequentUniversalModal polarity test subformula) hypersequents

        newHypersequents =
            addAllFormulasToFirstWorlds
            polarity (map subformula relevantFormulas) recursiveHypersequents
    in (World newSequent newHypersequents)

addAllFormulasToFirstWorlds :: Polarity -> [Formula] -> [Hypersequent] -> [Hypersequent]
addAllFormulasToFirstWorlds polarity formulas hypersequents =
    foldl (\newHypersequents formula ->
               addFormulaToAllFirstWorlds polarity formula newHypersequents) hypersequents formulas



addFormulaToAllFirstWorlds :: Polarity -> Formula -> [Hypersequent] -> [Hypersequent]
addFormulaToAllFirstWorlds polarity formula hypersequents =
    map (addFormulaToFirstWorld polarity formula) hypersequents

addFormulaToFirstWorld :: Polarity -> Formula -> Hypersequent -> Hypersequent
addFormulaToFirstWorld _ _ BranchEnd = BranchEnd
addFormulaToFirstWorld polarity formula (World sequent hypersequents) =
    (World (addFormulaToSequentWithPolarity polarity formula sequent) hypersequents)

hypersequentRightNecessity :: Hypersequent -> Hypersequent
hypersequentRightNecessity = hypersequentExistentialModal Positive necessityP necessity

hypersequentLeftPossibility :: Hypersequent -> Hypersequent
hypersequentLeftPossibility = hypersequentExistentialModal Negative possibilityP possibility

hypersequentExistentialModal :: Polarity -> (Formula -> Bool) -> (Formula -> Formula) -> Hypersequent -> Hypersequent
hypersequentExistentialModal _ _ _ BranchEnd = BranchEnd
hypersequentExistentialModal polarity test subformulaFn (World sequent hypersequents) =
    let positiveFormulas = posFormulas sequent
        negativeFormulas = negFormulas sequent
        (relevantFormulas, irrelevantFormulas) =
            case polarity of
              Positive -> (gatherFormulas test positiveFormulas)
              Negative -> (gatherFormulas test negativeFormulas)
        newHypersequents =
            map (\formula -> let firstSequent =
                                     case polarity of
                                       Positive -> makePositiveSequent . subformulaFn $ formula
                                       Negative -> makeNegativeSequent . subformulaFn $ formula
                             in (World firstSequent [BranchEnd]))
                relevantFormulas
        newSequent = case polarity of
                       Positive -> (makeSequent negativeFormulas irrelevantFormulas)
                       Negative -> (makeSequent irrelevantFormulas positiveFormulas)
        recursiveHypersequents = map
                                 (hypersequentExistentialModal polarity test subformulaFn)
                                 hypersequents
    in (World newSequent (newHypersequents ++ recursiveHypersequents))

-- Structural Rules
hypersequentFold :: (Hypersequent -> a) -> (Sequent -> [a] -> a) -> Hypersequent -> a
hypersequentFold endFn _ BranchEnd = endFn BranchEnd
hypersequentFold endFn worldFn (World seq hypersequents) =  worldFn seq (map (hypersequentFold endFn worldFn) hypersequents)

applyStructuralRules ::  System -> [ModalProofTree] -> [ModalProofTree]
applyStructuralRules system proofTrees = case system of
                                           K    -> proofTrees
                                           T    -> mapAppend contraction proofTrees
                                           Four -> mapAppend weakening proofTrees

-- Structural Rules Internals

-- @todo FAST-REMOVE-DUPLICATES -- This won't be fast because we can't sort hypersequents.

contraction :: ModalProofTree -> [ModalProofTree]
contraction = structuralRuleInternal Contraction

weakening :: ModalProofTree -> [ModalProofTree]
weakening = structuralRuleInternal Weakening

data StructralRule = Contraction | Weakening

structuralRuleInternal :: StructralRule -> ModalProofTree -> [ModalProofTree]
structuralRuleInternal _ Leaf = [Leaf]
structuralRuleInternal _ Close = [Close]
structuralRuleInternal rule (Node hypersequent [Leaf]) =
    map (\newHypersequent ->
             (Node hypersequent [(makeTreePossiblyClosingBranch newHypersequent)])) .
    (case rule of
       Contraction -> contractHypersequent
       Weakening   -> weakenHypersequent) $ hypersequent
structuralRuleInternal _ (Node hypersequent [Close]) = [(Node hypersequent [Close])]
structuralRuleInternal rule (Node hypersequent trees) =
    let newProofTrees = map (case rule of
                               Contraction -> contraction
                               Weakening   -> weakening) trees
    in (Node hypersequent trees):(map (\newTrees -> Node hypersequent newTrees) .
                                      cartesianProduct $
                                                       newProofTrees)

--- Contraction  Internals --

contractHypersequent :: Hypersequent -> [Hypersequent]
contractHypersequent hypersequent =
    let levelsToContract = range .  (\x -> x - 1) . hypersequentDepth $ hypersequent
    in mapAppend (\num -> contractLevelNNodes num hypersequent) levelsToContract

contractRootNode :: Hypersequent -> Hypersequent
contractRootNode BranchEnd = BranchEnd
contractRootNode (World seq [BranchEnd]) = (World seq [(World seq [BranchEnd])])
contractRootNode (World seq hypersequents) = (World seq ((World seq [BranchEnd]):hypersequents))

contractLevel1Nodes :: Hypersequent -> [Hypersequent]
contractLevel1Nodes BranchEnd = [BranchEnd]
contractLevel1Nodes (World seq []) = []
contractLevel1Nodes (World seq (hypersequent:hypersequents)) =
    contractLeve1NodesInternal [] hypersequents seq hypersequent

contractLeve1NodesInternal :: [Hypersequent] -> [Hypersequent] ->
                              Sequent -> Hypersequent -> [Hypersequent]
contractLeve1NodesInternal earlier [] seq hypersequent =
    [(World seq (earlier ++ [contractRootNode hypersequent]))]
contractLeve1NodesInternal earlier later rootSequent  hypersequent =
    let contractedHypersequent = contractRootNode hypersequent
        result = World rootSequent (earlier ++ (contractedHypersequent:later))
        recursiveCase =
            contractLeve1NodesInternal
            (earlier ++ [hypersequent]) (tail later) rootSequent (head later)
     in result:recursiveCase

contractLevelNNodes :: Int -> Hypersequent -> [Hypersequent]
contractLevelNNodes 0 hypersequent = [contractRootNode hypersequent]
contractLevelNNodes n hypersequent =
    operateOnLevelNNodes contractLevel1Nodes contractLevelNNodesHelper n hypersequent

contractLevelNNodesHelper :: Sequent -> [Hypersequent] -> Hypersequent -> (Int, [Hypersequent]) -> (Int, [Hypersequent])
contractLevelNNodesHelper seq hypersequents hypersequent (index,result) =
    let newHypersequents = replaceItemAtIndex hypersequent hypersequents index
        contractedHypersequent = (World seq newHypersequents)
    in if newHypersequents == hypersequents
       then ((index - 1), result)
       else ((index - 1), (contractedHypersequent:result))

-- Potentially Useful Abstraction

operateOnLevelNNodes :: (Hypersequent -> [Hypersequent]) -> (Sequent -> [Hypersequent] -> Hypersequent -> (Int, [Hypersequent]) -> (Int, [Hypersequent])) -> Int -> Hypersequent -> [Hypersequent]
--Helper is a function that operates on a hypersequent and generates a transformed hypersequent - it returns the next index and the updated results. It's probably an abstraction that could be used for the other structural rules, but I think this code is too abstracted to be understandible. We'll deal with bugs from code in multiple places or abstract elsewhwere if it ever becomes totally obvious what the right abstraction is.
operateOnLevelNNodes baseCase _ 1 hypersequent = baseCase hypersequent
operateOnLevelNNodes _ _ n BranchEnd = [BranchEnd]
operateOnLevelNNodes base helper n (World seq hypersequents) =
    let recursiveCase = mapAppend (operateOnLevelNNodes base helper (n - 1)) hypersequents
        finalIndex    = (length hypersequents) - 1
        (ignore, result) =
            foldr (\hypersequent (index,result) ->
                       helper seq hypersequents hypersequent (index, result))
            (finalIndex, []) recursiveCase
    in result



--- Weakening ---
weakenHypersequent :: Hypersequent -> [Hypersequent]
weakenHypersequent hypersequent =
    let levelsToWeaken = range .  (\x -> x - 1) . hypersequentDepth $ hypersequent
    in  hypersequent:(filter (\newHyper -> newHyper /= hypersequent) .
        mapAppend (\num -> weakenLevelNNodes num hypersequent) $ levelsToWeaken)


weakenLevel1Nodes :: Hypersequent -> [Hypersequent]
weakenLevel1Nodes BranchEnd = [BranchEnd]
weakenLevel1Nodes (World seq []) = []
weakenLevel1Nodes (World seq hypersequents) =
     let (ignoreEarlier, ignoreLater, result) =
             foldl (\(earlier, later, acc) hypersequent ->
                       case hypersequent of
                         BranchEnd ->
                             weakenLevel1NodesEmptyCase earlier later acc hypersequent seq
                         (World level1Seq level2Hypersequents) ->
                             if level1Seq == emptySequent
                             then
                                 let newEarlier = (snoc hypersequent earlier)
                                     newLater   = (myTail later)
                                     newHypers  = earlier ++ level2Hypersequents ++ later
                                     newAcc     = ((World seq newHypers):acc)
                                 in (newEarlier, newLater, newAcc)
                             else weakenLevel1NodesEmptyCase earlier later acc hypersequent seq)
                       ([], (myTail hypersequents), []) hypersequents
     in result

weakenLevel1NodesEmptyCase :: [Hypersequent] -> [Hypersequent] -> [Hypersequent] -> Hypersequent -> Sequent -> ([Hypersequent], [Hypersequent], [Hypersequent])
weakenLevel1NodesEmptyCase earlier later accumulator hypersequent baseSequent =
    let newEarlier = (snoc hypersequent earlier)
        newLater   =
            (myTail later)
        newHypers  =
            earlier ++ (hypersequent:later)
        newAcc     =
            (World baseSequent newHypers):accumulator

    in (newEarlier, newLater, newAcc)

weakenLevelNNodes :: Int -> Hypersequent -> [Hypersequent]
weakenLevelNNodes 1 hypersequent = weakenLevel1Nodes hypersequent
weakenLevelNNodes n BranchEnd = [BranchEnd]
weakenLevelNNodes n (World seq []) = []
weakenLevelNNodes n (World seq hypersequents) =
    let (ignoreEarlier, ignoreLater, result) =
            foldl (\(earlier, later, acc) hypersequent ->
                       let newEarlier = (snoc hypersequent earlier)
                           newLater   = (myTail later)
                           weakHypers = (weakenLevelNNodes (n - 1) hypersequent)
                           newHypers  = (map
                                        (\weakHyper ->
                                             (World seq (earlier ++ (weakHyper:later))))
                                        weakHypers)
                           newAcc     = newHypers ++ acc
                       in (newEarlier, newLater, newAcc))
                      ([],(myTail hypersequents), []) hypersequents
    in result



p   = makeAtom "p"
q   = makeAtom "q"
nec = Necessarily
pos = Possibly
ax  = (Implies
       (nec p)
       (nec (nec p)))

start = [(Node (makeStartingHypersequent (canonicalizeFormula ax)) [Leaf])]


lastOne (x:xs) = if xs == [] then x else lastOne xs
