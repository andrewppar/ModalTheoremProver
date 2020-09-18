module Model
    where
import Formula
import Sequent
import DepthFirstProver

---------------
---- Models ---
---------------

type Model = ([Formula],[Formula])

makeModel :: [Formula] -> [Formula] -> Model
makeModel negForms posForms = (negForms, posForms)

atomicModelP :: Model -> Bool
atomicModelP (negForms, posForms) = [] == filter nonAtomicFormulaP (negForms ++ posForms)

getAtomicModel :: Model -> Model
getAtomicModel (negForms, posForms) = makeModel (f negForms) (f posForms)
                                      where f = filter atomicFormulaP

generateAtomicModelFromFailedProof :: PropProofTree -> Model
generateAtomicModelFromFailedProof prooftree = getAtomicModel . makeModelFromSequent . firstOpenLeaf $ prooftree

firstOpenLeaf :: PropProofTree -> Sequent
firstOpenLeaf Leaf = makeSequent [] []
firstOpenLeaf Close = makeSequent [] []
firstOpenLeaf (Node seq [Leaf]) = seq
firstOpenLeaf (Node seq [Close]) = makeSequent [] []
firstOpenLeaf (Node seq trees) = head (map firstOpenLeaf trees) -- This is wrong!!! We need something that only gets the first element of a list meeting criterion, but I couldn't think how to do this. This is totally something haskell's lazy evaluation can handle.


makeModelFromSequent :: Sequent -> Model
makeModelFromSequent (Sequent a b) = makeModel a b
