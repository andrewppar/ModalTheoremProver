module Hypersequent
    (Hypersequent (..)
    , hypersequentDepth
    , makeStartingHypersequent
    , everyInHypersequent
    , hypersequentBaseAtomicFormulas
    , emptyHypersequent
    , purelyModalOrAtomicHypersequentP
    , gatherAtomicSentencesByPolarity
)
    where

import Utilities
import Formula
import Canonicalizer
import Sequent

data Hypersequent = BranchEnd | World Sequent [Hypersequent] deriving (Eq, Show)
-- We're not going to use the Tree structure because it is too overloaded even though this really is just a tree

--instance Show Hypersequent where
 --   show hypersequent = showHypersequent hypersequent 0

showHypersequent :: Hypersequent -> Int -> String
showHypersequent BranchEnd depth = (replicate depth ' ') ++ "B\n"
showHypersequent (World seq hypersequents) depth =
    (replicate depth ' ') ++ (show seq ) ++ "\n" ++
                              (joinStrings " " (map
                                                (\hypersequent ->
                                                     showHypersequent hypersequent (5+ depth))
                                                hypersequents))

everyInHypersequent :: (Sequent -> Bool) -> Hypersequent -> Bool
everyInHypersequent _ BranchEnd = True
everyInHypersequent predicate (World sequent hypersequents) =
    if predicate sequent
    then generalizedConjunction . (map (everyInHypersequent predicate)) $ hypersequents
    else False

hypersequentDepth :: Hypersequent -> Int
hypersequentDepth BranchEnd = 0
hypersequentDepth (World seq hypersequents) =
    1 + (maximum . (map hypersequentDepth) $ hypersequents)

makeStartingHypersequent :: Formula -> Hypersequent
makeStartingHypersequent formula = World (makePositiveSequent formula) [BranchEnd]

emptyHypersequent :: Hypersequent
emptyHypersequent = (World emptySequent [BranchEnd])

hypersequentBaseAtomicFormulas :: Hypersequent -> Polarity -> [Formula]
hypersequentBaseAtomicFormulas BranchEnd _ = []
hypersequentBaseAtomicFormulas (World seq hypersequents) polarity =
   sequentAtomicFormulasByPolarity seq polarity

purelyModalOrAtomicHypersequentP :: Hypersequent -> Bool
purelyModalOrAtomicHypersequentP BranchEnd = True
purelyModalOrAtomicHypersequentP (World seq hypersequents) =
    (purelyModalOrAtomicSequentP seq)
    && (generalizedConjunction . map purelyModalOrAtomicHypersequentP $ hypersequents)


gatherAtomicSentencesByPolarity :: Polarity -> Hypersequent -> [Formula]
gatherAtomicSentencesByPolarity _ BranchEnd = []
gatherAtomicSentencesByPolarity polarity (World seq hypersequents) =
    let atomsInSeq = filter atomicFormulaP . (case polarity of
                                                Positive -> posFormulas
                                                Negative -> negFormulas) $ seq
    in atomsInSeq ++ (mapAppend (gatherAtomicSentencesByPolarity polarity) hypersequents)
