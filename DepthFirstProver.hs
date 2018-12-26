import Control.Parallel
import Control.Parallel.Strategies
import Data.Char
    
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
                        
joinStrings :: String -> [String] -> String
joinStrings _ [] = " "               
joinStrings stringToInsert (x:xs) = x ++ (foldl (\string accumulator -> string ++ stringToInsert ++  accumulator) "" xs)
                        
instance Show Formula where
    show (AtomicFormula string) = show string ++ " "
    show (And conjuncts) = "(And " ++ (joinStrings " " . map show) conjuncts ++ ")"
    show (Or disjuncts)  = "(Or " ++  (joinStrings  " " . map show) disjuncts ++ ")"
    show (Implies antecedent consequent) = "(Implies " ++ (show antecedent) ++ (show consequent) ++ ")"
    show (Not negatum) = "(Not " ++ show negatum ++ ")"
    show (Possibly possibility) = "(M " ++ show possibility ++ ")"
    show (Necessarily necessity) = "(L " ++ show necessity ++ ")"

---- Constructing Formulas                                    

equiv :: Formula -> Formula -> Formula
equiv a b = (And [(Implies a b), (Implies b a)])

makeAtom :: String -> Formula
makeAtom string = AtomicFormula string

---- Predicates

atomicFormulaP :: Formula -> Bool
atomicFormulaP (AtomicFormula x) = True
atomicFormulaP _ = False

nonAtomicFormulaP :: Formula -> Bool
nonAtomicFormulaP = not . atomicFormulaP                     

disjunctionP :: Formula -> Bool
disjunctionP (Or disjuncts) = True
disjunctionP _ = False

conjunctionP :: Formula -> Bool
conjunctionP (And conjuncts) = True
conjunctionP _ = False

negationP :: Formula -> Bool
negationP (Not negatum) = True
negationP _ = False

possibilityP :: Formula -> Bool
possibilityP (Possibly possibility) = True
possibilityP _ = False

necessityP :: Formula -> Bool
necessityP (Necessarily necessity) = True
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

{-| Canonicalizer |-}

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
    (replicate depth ' ') ++ (show a ) ++ "\n" ++
                              (joinStrings " " (map (\tree -> showTree tree (5+ depth)) trees)) 

class ProofTree a where
    axiomP                 :: a -> Bool
    gatherLeafNodes     :: Tree a -> [a]

    gatherLeafNodes Leaf = []
    gatherLeafNodes Close = []
    gatherLeafNodes (Node seq [Leaf]) = [seq]
    gatherLeafNodes (Node seq [Close]) = [seq]
    gatherLeafNodes (Node seq trees) = mapAppend gatherLeafNodes trees


data ProofTreeStatus = Proven | NotProven | CounterExampleGenerated | Continue deriving (Show,Eq)


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

gatherConjunctions :: [Formula] -> ([Formula],[Formula])
gatherConjunctions = gatherFormulas conjunctionP

gatherDisjunctions :: [Formula] -> ([Formula],[Formula])
gatherDisjunctions = gatherFormulas disjunctionP

gatherNegations :: [Formula] -> ([Formula],[Formula])
gatherNegations = gatherFormulas negationP                   

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


--------------------------------------
--- Canonical Ordering Of Formulas ---
--------------------------------------

---Use this to turn setIntersection from N^2 generally to N Log N generally.

sortFormulas :: [Formula] -> [Formula]
sortFormulas [] = []
sortFormulas (x:xs) =
    let smaller = sortFormulas [form | form <- xs, formulaLessThanOrEqual form x]
        bigger  = sortFormulas [form | form <- xs, not (formulaLessThanOrEqual form x)]
    in smaller ++ [x] ++ bigger

                
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


{-| Modal Logic |-}

data System = K 

data Hypersequent = BranchEnd | World Sequent [Hypersequent] deriving (Eq, Show)
-- We're not going to use the Tree structure because it is too overloaded even though this really is just a tree

--hypersequentShow :: Hypersequent -> Int -> String
--hypersequentShow                     
                  

                  
type ModalProofTree = Tree Hypersequent

---------------------
--- Hypersequents ---
---------------------
gatherModalOpenLeafNodes :: ModalProofTree -> [Hypersequent]
gatherModalOpenLeafNodes Leaf = []
gatherModalOpenLeafNodes Close = []
gatherModalOpenLeafNodes (Node seq [Leaf]) = [seq]
gatherModalOpenLeafNodes (Node seq [Close]) = []
gatherModalOpenLeafNodes (Node seq trees) = mapAppend gatherModalOpenLeafNodes trees


everyInHypersequent :: (Sequent -> Bool) -> Hypersequent -> Bool
everyInHypersequent _ BranchEnd = True
everyInHypersequent predicate (World sequent hypersequents) =
    if predicate sequent
    then generalizedConjunction . (map (everyInHypersequent predicate)) $ hypersequents
    else False
                           
-- we revamped what a hyperseuqent is. All this needs to get rewritten.
makeStartingHypersequent :: Formula -> Hypersequent
makeStartingHypersequent formula = World (makePositiveSequent formula) [BranchEnd]

emptyHypersequent :: Hypersequent
emptyHypersequent = (World emptySequent [BranchEnd])

hypersequentAxiomP :: Hypersequent -> Bool
hypersequentAxiomP BranchEnd = False
hypersequentAxiomP (World sequent hypersequents) =
    if axiomP sequent
    then True
    else generalizedDisjunction . (map hypersequentAxiomP) $ hypersequents

                                                                         
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
    case (getModalProofTreeStatus tree system) of
      Proven -> (tree, Proven)
      CounterExampleGenerated -> (tree, CounterExampleGenerated)
      otherwise -> surveyProofTreesForStatus trees system

getModalProofTreeStatus :: ModalProofTree -> System -> ProofTreeStatus
getModalProofTreeStatus tree system =
    let openLeafNodes = (gatherModalOpenLeafNodes tree)
    in if openLeafNodes == []
       then Proven
       else if leafNodesContainModalCounterExampleP openLeafNodes system
       then CounterExampleGenerated
       else NotProven
      
leafNodesContainModalCounterExampleP :: [Hypersequent] -> System -> Bool
leafNodesContainModalCounterExampleP hypersequents system =
    anyInListMeetsCriteria groundHypersequentP hypersequents

groundHypersequentP :: Hypersequent -> Bool
groundHypersequentP = everyInHypersequent atomicSequentP

proveK :: Formula -> Bool
proveK formula = modalProve formula K          
    
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
modalProveOneStep trees system =
    let innerProveOneStep = map applyInnerRules trees
    in  applyStructuralRules innerProveOneStep system
--       
applyInnerRules :: ModalProofTree -> ModalProofTree
applyInnerRules =
                  applyLeftNecessity .
                  applyRightPossibility .
                  applyLeftPossibility .
                  applyRightNecessity .
                  (applyPropositionalRule hypersequentLeftConjunction) .
                  (applyPropositionalRule hypersequentRightDisjunction) .
                  (applyPropositionalRule hypersequentLeftNegation) .
                  (applyPropositionalRule hypersequentRightNegtaion) .
                  (applyPropositionalRule hypersequentRightConjunction) .
                  (applyPropositionalRule hypersequentLeftDisjunction) 
         
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
makeTreePossiblyClosingBranch hypersequent = (Node hypersequent (if hypersequentAxiomP hypersequent
                                                                 then [Close]
                                                                 else [Leaf]))
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
    in if nullResult
       then (Node hypersequent [Leaf])
       else (Node hypersequent [(Node newHypersequent [Leaf])]) 
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
            case polarity of
              Positive -> gatherFormulas test positiveFormulas
              Negative -> gatherFormulas test negativeFormulas
        newSequent = case polarity of
                       Positive -> makeSequent negativeFormulas irrelevantFormulas
                       Negative -> makeSequent irrelevantFormulas positiveFormulas
        recursiveHypersequents =
            map (hypersequentUniversalModal polarity test subformula) hypersequents
        newHypersequents =
            addAllFormulasToFirstWorlds polarity (map subformula relevantFormulas) recursiveHypersequents
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
applyStructuralRules :: [ModalProofTree] -> System -> [ModalProofTree]
applyStructuralRules proofTrees system = case system of
                                           K -> proofTrees


contraction :: [ModalProofTree] -> [ModalProofTree]
contraction = mapAppend allPossibleContractions

data ContractionMap = End | Bool | Point Bool [ContractionMap] deriving (Eq, Show)

newContractionMapForHypersequent :: Hypersequent -> ContractionMap
newContractionMapForHypersequent BranchEnd = End
newContractionMapForHypersequent (World sequent hypersequents) =
    (Point False (map newContractionMapForHypersequent hypersequents))

allPossibleContractions :: ModalProofTree -> [ModalProofTree]
allPossibleContractions Leaf = [Leaf]
allPossibleContractions Close = [Close]
allPossibleContractions (Node hypersequent [Leaf]) =
    let newHypersequents = allHypersequentContractions hypersequent
    in  map (\newHypersequent ->
                 (Node hypersequent [newHypersequent [Leaf]])) newHypersequents
      
allHypersequentContractions :: Hypersequent -> [Hypersequent]
allHypersequentContractions hypersequent =
    let contractionRange = range . worldCount $ hypersequent
    in mapAppend allContractionsOfNWorlds hypersequent) contractionRange

allContractionsOfNWorlds :: Hypersequent -> Int -> [Hypersequent]       

-----------------------
--- Misc. Utilities ---
-----------------------

setIntersection :: (Eq a) => [a] -> [a] -> [a]
setIntersection xs ys = foldr (\x acc -> if (elem x ys) then x:acc else acc) [] xs

emptyListP :: [a] -> Bool
emptyListP [] = True
emptyListP _  = False                
              
append :: [a] -> [a] -> [a] 
append xs ys = foldr (\x acc -> x:acc) ys xs -- @note: this reverses the order of the xs

mapAppend :: (a -> [b]) -> [a] -> [b]                        
mapAppend f xs = foldr (\x acc -> x ++ acc) [] $ map f xs

generalizedConjunction :: [Bool] -> Bool
generalizedConjunction = generalizedJunction True (&&)

generalizedDisjunction :: [Bool] -> Bool
generalizedDisjunction = generalizedJunction False (||)                          

generalizedJunction :: Bool  -> (Bool -> Bool -> Bool) -> [Bool] -> Bool
generalizedJunction base _ [] = base
generalizedJunction base booleanFunction (x:xs) =                              
                      (booleanFunction x (generalizedJunction base booleanFunction xs)) 

anyInListMeetsCriteria :: (a -> Bool) -> [a] -> Bool
anyInListMeetsCriteria _ [] = False
anyInListMeetsCriteria f (x:xs) = if f x
                                 then True
                                 else anyInListMeetsCriteria f xs

addEachToEachInList :: [a] -> [[a]] -> [[a]] --We use this in the canonoicalizer, but I bet it's wrong probably it should be addToEach, changing it doesn't cause any tests to fail. @todo investigate
addEachToEachInList xs [] = [xs]
addEachToEachInList xs (y:ys) =
    let newAdditions = map (:y) xs
    in  newAdditions ++ (addEachToEachInList xs ys)



cartesianProduct :: [[a]] -> [[a]]  -- @todo make this recursive 
cartesianProduct [] = []
cartesianProduct [xs] = map (\x -> [x]) xs                    
cartesianProduct (x:xs) =
    let recursiveCase = cartesianProduct xs
    in addToEach x recursiveCase

addToEach :: [a] -> [[a]] -> [[a]]
addToEach _ [] = []
addToEach xs (y:ys) =
    let newAdditions = map (:y) xs
    in  newAdditions ++ (addToEach xs ys)

addToEachWithBase :: [a] -> [[a]] -> [[a]]
addToEachWithBase [] ys = ys
addToEachWithBase xs [] = [xs]
addToEachWithBase (x:xs) ys =
    let recursiveCase = addToEachWithBase xs ys
    in  map (x:) recursiveCase

removeDuplicates :: (Eq a) => [a] -> [a]
removeDuplicates [] = []
removeDuplicates (x:[]) = [x]
removeDuplicates (x:y:zs) = if x == y
                            then (y:(removeDuplicates zs))
                            else (x: (removeDuplicates (y:zs)))

{-| Parallel Experiment |-}

parallelMap :: (a -> b) -> [a] -> [b]
parallelMap _ [] = []
parallelMap f (x:xs) = par a (pseq b (a:b))
    where a = f x
          b = parallelMap f xs


badFib :: Int -> Int
badFib 0 = 1
badFib 1 = 1
badFib n =  a +  b
    where a = (badFib (n - 2))
          b = (badFib (n - 1))
           

check1 = (parMap rdeepseq) badFib (replicate 5 40)              
check2 = map badFib (replicate 5 40)
main = runAllTestsVerbose 
              
{-| Testing |-}

type Verbosity = String

testCase :: (Eq b) => (a -> b) -> a -> b -> Bool
testCase f input output = (f input) == output

showTestCase :: (Show a) => (Show b) => (Eq b) => (a -> b) -> a -> b -> IO ()
showTestCase function input output = let result = function input
                                         bool   = result == output
                                     in do putStrLn ( "Input: " ++ (show input))
                                           putStrLn ("Desired: " ++ (show output))
                                           if bool
                                           then putStrLn "Success"
                                           else do putStrLn "Failure"
                                                   putStrLn ("Actual: " ++ (show result))
                                           putStrLn "" 

testCaseTable :: (Eq b) => (a -> b) -> [(a,b)] -> Bool
testCaseTable function inputOutputPairs = (foldr (\(input,output) success -> if (testCase function input output) then (success && True) else (success && False))) True inputOutputPairs

testCaseTableVerbose :: (Eq b, Show a, Show b) => (a -> b) -> [(a,b)] -> IO ()
testCaseTableVerbose function inputOutputPairs = sequence_ (map (\(input,output) -> showTestCase function input output) inputOutputPairs)

---------------- Run All Tests
allTests :: [Bool]
allTests = [canonicalizerTest,
           proveTest,
           proofStatusTest,
           gatherConjunctionsTest,
           addConjunctsTest,
           classicalRightConjunctionTest,
           classicalLeftDisjunctionTest,
           classicalLeftConjunctionTest,
           classicalLeftNegationTest,
           cartesianProductTest,
           proveKTest,
           generalizedConjunctionTest,
           generalizedDisjunctionTest
           ]

allTestsWithName :: [(String,Bool)]
allTestsWithName = zip ["canonicalierTest",
                        "proveTest",
                        "proofStatusTest",
                        "gatherConjunctionTest",
                        "addConjunctsTest",
                        "classicalRightConjunctionTest",
                        "classicalLeftDisjunctionTest",
                        "classicalLeftConjunctionTest",
                        "classicalLeftNegation",
                        "cartesianProductTest",
                        "proveKTest",
                        "generalizedConjunctionTest",
                        "generalizedDisjunctionTest"
                        
                        ]
                   allTests
                       
          
runAllTests :: Bool
runAllTests = generalizedConjunction allTests

runAllTestsVerbose :: IO ()
runAllTestsVerbose = let testRuns = map (\testWithName ->
                                             let result = snd testWithName
                                             in (result,
                                                 putStrLn $ "Running " ++ (fst testWithName) ++ "...  " ++ (show result))) allTestsWithName
                         finalResult = generalizedConjunction (map fst testRuns) 
                     in do
                       sequence_ (map snd testRuns)
                       putStrLn ""
                       putStrLn $ "Overall Result: " ++ (show finalResult)
        
                  
                        

----- Canonicalizer Tests

canonicalizerTest :: Bool
canonicalizerTest = testCaseTable canonicalizeFormula canonicalizerTestCaseTable

canonicalizerTestVerbose :: IO ()                    
canonicalizerTestVerbose = testCaseTableVerbose canonicalizeFormula canonicalizerTestCaseTable
                                                 
canonicalizerTestCaseTable :: [(Formula,Formula)]
canonicalizerTestCaseTable = [
 ((Not (Not (AtomicFormula "a"))),
  (AtomicFormula "a")
 ),
 
 ((Implies (AtomicFormula "a") (AtomicFormula "b")),
  (Or [(AtomicFormula "b"), (Not (AtomicFormula "a"))])
 ),

 ((Not (Possibly (makeAtom "a"))),
  (Necessarily (Not (makeAtom "a")))
 ),

 ((Not (Necessarily (makeAtom "a"))),
  (Possibly (Not (makeAtom "a")))
  ),
  
                                 

 ((Not (Not (Not (Not (AtomicFormula "a"))))),
  (AtomicFormula "a")
  ),
 
 ((And [(Or [(AtomicFormula "a"), (AtomicFormula "b")]),
        (AtomicFormula "c")]),
  (And [(makeAtom "c"), (Or [(makeAtom "a"), (makeAtom "b")])])
 ),
  
 ((And [(Or [(AtomicFormula "a"), (Not (AtomicFormula "c"))])]),
  (Or [(AtomicFormula "a"), (Not (AtomicFormula "c"))])
  ),
  
 ((And [(Or [(AtomicFormula "a"), (AtomicFormula "b")]), (Or [(AtomicFormula "c"), (AtomicFormula "d")])]),
  (And [(Or [(AtomicFormula "a"), (AtomicFormula "b")]), (Or [(AtomicFormula "c"), (AtomicFormula "d")])])
  ), 

  ((And
    [(Implies (Not (AtomicFormula "a")) (Not (AtomicFormula "c"))),
     (Or [(Not (Not (AtomicFormula "a"))), (Not (AtomicFormula "c"))])]),

    (Or [(makeAtom "a"), (Not (makeAtom "c"))])),

  ((Implies (Implies (Not (Implies (makeAtom "a") (makeAtom "c"))) (makeAtom "b"))
           (Implies (makeAtom "a") (Implies (Not (makeAtom "b")) (makeAtom "c")))),
  (Or [(Or [(Not (makeAtom "a")), (Or [(makeAtom "b"), (makeAtom "c")])]),
       (And [(Not (makeAtom "b")), (And [(makeAtom "a"), (Not (makeAtom "c"))])])])
  ),

 ((Possibly (Or [(AtomicFormula "p"), (Not (AtomicFormula "p"))])),
  (Or [(Possibly (AtomicFormula "p")), (Possibly (Not (AtomicFormula "p")))])
  ),

 ((Necessarily (Or [(AtomicFormula "p"), (Not (AtomicFormula "p"))])),
  (Necessarily (Or [(AtomicFormula "p"), (Not (AtomicFormula "p"))]))
  )
 ]

------- Formula Tests
formulaSetsEqualPTest :: Bool 
formulaSetsEqualPTest = 
 testCaseTable formulaSetsEqualPHelper formulaSetsEqualPTestCaseTable 

formulaSetsEqualPTestVerbose :: IO () 
formulaSetsEqualPTestVerbose = 
 testCaseTableVerbose formulaSetsEqualPHelper formulaSetsEqualPTestCaseTable

formulaSetsEqualPHelper :: ([Formula], [Formula]) -> Bool
formulaSetsEqualPHelper (formsOne, formsTwo) = formulaSetsEqualP formsOne formsTwo

formulaSetsEqualPTestCaseTable :: [(([Formula],[Formula]),Bool)] 
formulaSetsEqualPTestCaseTable =
    let p = makeAtom "p"
        q = makeAtom "q"
        notP = (Not p)
        notQ =  (Not q)
        impliesPQ = (Implies p q)
    in [(([p,q],
          [q,p]),
        True),

        (([p,q,q],
          [p,q]),
         True),

        (([p,q,q],
          [q,p]),
         True),

        (([impliesPQ, notP],
          [impliesPQ, notQ]),
         False),

        (([impliesPQ, notP, notQ, p],
          [impliesPQ, notQ, p, notP]),
         True)
        ]

        

------- Proof tests

proveTest :: Bool
proveTest = testCaseTable propositionalProve propositionalProveTestCaseTable

proveTestVerbose :: IO ()
proveTestVerbose = testCaseTableVerbose propositionalProve propositionalProveTestCaseTable

propositionalProveTestCaseTable :: [(Formula,Bool)]
propositionalProveTestCaseTable = [ ((Or [(AtomicFormula "p"), (Not (AtomicFormula "p"))]),
                      True),
                       
                       ((Not (And [(AtomicFormula "p"), (Not (AtomicFormula "p"))])), 
                      True),
                       
                       ((And [(Implies (Not (AtomicFormula "a")) (Not (AtomicFormula "c"))), (Or [(Not (Not (AtomicFormula "a"))), (Not (AtomicFormula "c"))])]),
                        False),
                       
                         ((AtomicFormula "a"),
                          False),

                         ((equiv (Not (Not (Not (AtomicFormula "a")))) (AtomicFormula "a")),
                          False),

                         
                         ((equiv (AtomicFormula "a") (Or [(AtomicFormula "a"), (Not (AtomicFormula "a"))])),
                          False),

                        ((Implies (AtomicFormula "a") (Or [(AtomicFormula "a"), (Not (AtomicFormula "a"))])),
                                                                                                                              True),

                        ((equiv (Implies (Not (Implies (makeAtom "a") (makeAtom "c"))) (makeAtom "b"))
                               (Implies (makeAtom "a") (Implies (Not (makeAtom "b")) (makeAtom "c")))),
                         True),
                        

                        ((Or [(Or [(AtomicFormula "a"), (AtomicFormula "b")]), (Not (AtomicFormula "a"))]),
                         True),
                        
                       
                       ((Implies (AtomicFormula "a") (AtomicFormula "a")),
                       True),

                       ((Implies (And [(makeAtom "a"),
                                       (Implies (makeAtom "a") (makeAtom "b")),
                                       (Implies (makeAtom "b") (makeAtom "c"))])
                                 (makeAtom "c")),
                        True),

                       ((equiv (equiv (makeAtom "p") (makeAtom "q")) (equiv (makeAtom "q") (makeAtom "p"))), 
                                                                                                                             True),

                       ((Implies (And [(Or [(makeAtom "p"), (makeAtom "q")]),
                                       (Implies (makeAtom "p") (Not(makeAtom "q")))])
                                 (Implies (Implies (makeAtom "p") (makeAtom "q"))
                                          (And [(makeAtom "q"), (Not (makeAtom "p"))]))),
                        True),
                                   

                        ((And [(Implies (Not (Or [(AtomicFormula "a"), (AtomicFormula "b")]))
                                      (And [(Not (AtomicFormula "a")), (Not (AtomicFormula "b"))])),
                             (Implies (And [(Not (AtomicFormula "a")), (Not (AtomicFormula "b"))])
                      
                                      (Not (Or [(AtomicFormula "a"), (AtomicFormula "b")])))]),
                         True),

                        ((equiv (And [(AtomicFormula "a"), (AtomicFormula "b")]) (Not (Or [(Not (AtomicFormula "a")), (Not (AtomicFormula "b"))]))),
                         True),

                        ((Implies
                          (And
                           [(equiv (makeAtom "TVAI-1") (Implies (And [(makeAtom "A"), (makeAtom "B")]) (makeAtom "C"))),
                            (equiv (makeAtom "TVAI-2") (Implies (And [(makeAtom "A"), (makeAtom "D")]) (makeAtom "C"))),
                            (makeAtom "TVAI-1"),
                            (Implies (makeAtom "D") (makeAtom "B"))])
                           (makeAtom "TVAI-2")),
                         True),

                        ((equiv (And [(AtomicFormula "p")]) (AtomicFormula "p")), 
                         True),
                        ((Implies (Implies (Implies (AtomicFormula "p") (AtomicFormula "q")) (AtomicFormula "p")) (AtomicFormula "p")),
                                                                                                                                                        True)
                     ] 

proveKTest :: Bool
proveKTest = testCaseTable proveK proveKTestCaseTable

proveKTestVerbose :: IO ()             
proveKTestVerbose = testCaseTableVerbose proveK proveKTestCaseTable             

proveKTestCaseTable :: [(Formula, Bool)]
proveKTestCaseTable = let atomP = makeAtom "p"
                          atomQ = makeAtom "q"
                          nec   = Necessarily
                          pos   = Possibly
                      in [
                       ((nec
                         (Or [(Not atomP), atomP])),
                         True),

                       ((Implies
                          (nec (Implies atomP atomQ))
                          (Implies (nec atomP) (nec atomQ))),
                        True),

                       ((Not (pos (And [(Not atomP), atomP]))),
                         True),

                       ((Not (nec (Not (And [(Not atomP), atomP])))),
                         False),

                       ((nec
                         (Implies atomP (Or [atomP, atomQ]))),
                        True),

                       ((Implies
                         (nec atomP)
                         (nec (Or [atomP, atomQ]))),
                        True),

                       ((nec
                         (equiv
                          (Not (nec atomP))
                          (pos (Not atomP)))),
                        True),

                       ((nec
                         (equiv
                          (Not (pos atomP))
                          (nec (Not atomP)))),
                        True),

                        ((Implies
                          (pos
                           (Implies atomP atomQ))
                          (Implies
                           (nec atomP)
                          (pos atomQ))),
                        True),
                    
                       ((Implies
                        (nec atomP)
                        (nec (Or [atomP, atomQ]))),
                        True)

                         ]

---- Utility Tests

proofStatusTest :: Bool
proofStatusTest = testCaseTable proofStatusSum proofStatusTestCaseTable

proofStatusTestVerbose :: IO ()
proofStatusTestVerbose =
    testCaseTableVerbose proofStatusSum proofStatusTestCaseTable                          

                             

proofStatusTestCaseTable :: [([ProofTreeStatus],ProofTreeStatus)]
proofStatusTestCaseTable = [
 ([Proven, Proven, Proven],
                          Proven),
 ([Proven, NotProven, Proven, Proven, Proven],
                                             NotProven),
 ([Proven, NotProven, Proven, NotProven, CounterExampleGenerated],
                                                                 CounterExampleGenerated),
 ([Proven, NotProven, CounterExampleGenerated, Proven, NotProven],
                                                                 CounterExampleGenerated),
 ([CounterExampleGenerated, Proven, NotProven, Proven, NotProven], 
                                                                 CounterExampleGenerated)]


gatherConjunctionsTest :: Bool 
gatherConjunctionsTest =
    testCaseTable gatherConjunctions gatherConjunctionsTestCaseTable 

gatherConjunctionsTestVerbose :: IO () 
gatherConjunctionsTestVerbose =
    testCaseTableVerbose gatherConjunctions gatherConjunctionsTestCaseTable

gatherConjunctionsTestCaseTable :: [([Formula], ([Formula], [Formula]))] 
gatherConjunctionsTestCaseTable =
    let p = makeAtom "p"
        q = makeAtom "q"
    in [
     ([p],
      ([],[p])),

     ([p,q],
      ([], [q,p])),

     ([(Or [p]), (And [q])],
      ([(And [q])], [(Or [p])])),

     ([(And [q]), p],
      ([(And [q])], [p]))
     ]
 
addConjunctsTest :: Bool 
addConjunctsTest = testCaseTable addConjunctsTestHelper addConjunctsTestCaseTable 

addConjunctsTestVerbose :: IO () 
addConjunctsTestVerbose = testCaseTableVerbose addConjunctsTestHelper addConjunctsTestCaseTable

addConjunctsTestHelper :: ([Formula], Sequent) -> [Sequent]
addConjunctsTestHelper pairs = let (formulas,sequent) = pairs
                               in addConjuncts formulas sequent

addConjuncts :: [Formula] -> Sequent -> [Sequent]
addConjuncts formulas sequent =
    addJuncts Positive conjuncts formulas sequent

addConjunctsTestCaseTable :: [(([Formula], Sequent),[Sequent])] 
addConjunctsTestCaseTable =
     let p = makeAtom "p"
         q = makeAtom "q"
         r = makeAtom "r"
         s = makeAtom "s"
         t = makeAtom "t"
         u = makeAtom "u"    
         andPQ = (And [p,q])
         andRS = (And [r,s])
         testSequent1 = makeSequent [t] [u] 
         testSequent2 = makeSequent [] [u]
         testSequent3 = makeSequent [t] []
         testSequent4 = emptySequent
     in [
      (([],testSequent1),
        [testSequent1]),

      (([], testSequent2),
        [testSequent2]),

      (([], testSequent3),
        [testSequent3]),

      (([], testSequent3),
        [testSequent3]),

      (([andPQ], testSequent1),
        [(makeSequent [t] [p,u]),
         (makeSequent [t] [q,u])]),

      (([andPQ], testSequent2),
        [(makeSequent [] [p,u]),
         (makeSequent [] [q,u])]),

      (([andPQ], testSequent3),
        [(makeSequent [t] [p]),
         (makeSequent [t] [q])]),

      (([andPQ], testSequent4),
        [(makeSequent [] [p]),
         (makeSequent [] [q])]),

      (([andPQ,andRS], testSequent1),
        [(makeSequent [t] [p,s,u]),
         (makeSequent [t] [q,s,u]),
         (makeSequent [t] [p,r,u]),
         (makeSequent [t] [q,r,u])]),

      (([andPQ,andRS], testSequent2),
        [(makeSequent [] [p,s,u]),
         (makeSequent [] [q,s,u]),
         (makeSequent [] [p,r,u]),
         (makeSequent [] [q,r,u])]),

      (([andPQ,andRS], testSequent3),
        [(makeSequent [t] [p,s]),
         (makeSequent [t] [q,s]),
         (makeSequent [t] [p,r]),
         (makeSequent [t] [q,r])]),

       (([andPQ,andRS], testSequent4),
        [(makeSequent [] [p,s]),
         (makeSequent [] [q,s]),
         (makeSequent [] [p,r]),
         (makeSequent [] [q,r])]) 
      ]
      

classicalRightConjunctionTest :: Bool 
classicalRightConjunctionTest = 
 testCaseTable classicalRightConjunction classicalRightConjunctionTestCaseTable 

classicalRightConjunctionTestVerbose :: IO () 
classicalRightConjunctionTestVerbose = 
 testCaseTableVerbose classicalRightConjunction classicalRightConjunctionTestCaseTable

classicalRightConjunctionTestCaseTable :: [([Sequent],[Sequent])] 
classicalRightConjunctionTestCaseTable = 
     let p = makeAtom "p"
         q = makeAtom "q"
         r = makeAtom "r"
         s = makeAtom "s"
         t = makeAtom "t"
         u = makeAtom "u"
         v = makeAtom "v"
         w = makeAtom "w"
         andPQ = (And [p,q])
         andRS = (And [r,s])
         testSequent1 = makeSequent [t] [u, andPQ]
         testSequent2 = makeSequent [v] [w]
         testSequent3 = makeSequent [v] [w, andRS]
         testSequent4 = makeSequent [v, andRS] [w]
         resultSequent1 = makeSequent [t] [p,u]
         resultSequent2 = makeSequent [t] [q,u]
     in [([testSequent1],
         [(makeSequent [t] [p,u]),
          (makeSequent [t] [q,u])]),

         ([testSequent1, testSequent2],
          [testSequent2,
           resultSequent1,
           resultSequent2]),

         ([testSequent1, testSequent3],
          [(makeSequent [v] [r,w]),
           (makeSequent [v] [s,w]), 
           resultSequent1,
           resultSequent2
           ]),

         ([testSequent2, testSequent4],
          [testSequent4, testSequent2])
         ]

classicalLeftDisjunctionTest :: Bool 
classicalLeftDisjunctionTest = 
 testCaseTable classicalLeftDisjunction classicalLeftDisjunctionTestCaseTable 

classicalLeftDisjunctionTestVerbose :: IO () 
classicalLeftDisjunctionTestVerbose = 
 testCaseTableVerbose classicalLeftDisjunction classicalLeftDisjunctionTestCaseTable

classicalLeftDisjunctionTestCaseTable :: [([Sequent],[Sequent])] 
classicalLeftDisjunctionTestCaseTable = 
     let p = makeAtom "p"
         q = makeAtom "q"
         r = makeAtom "r"
         s = makeAtom "s"
         t = makeAtom "t"
         u = makeAtom "u"
         v = makeAtom "v"
         w = makeAtom "w"
         orPQ = (Or [p,q])
         orRS = (Or [r,s])
         testSequent1 = makeSequent [t, orPQ] [u]
         testSequent2 = makeSequent [v] [w] 
         testSequent3 = makeSequent [v, orRS] [w]
         testSequent4 = makeSequent [v] [w, orRS]
         resultSequent1 = makeSequent [p,t] [u]
         resultSequent2 = makeSequent [q,t] [u]
     in [([testSequent1],
         [resultSequent1,
          resultSequent2]),

         ([testSequent1, testSequent2],
          [testSequent2,
           resultSequent1,
           resultSequent2]),

         ([testSequent1, testSequent3],
          [(makeSequent [r,v] [w]),
           (makeSequent [s,v] [w]), 
           resultSequent1,
           resultSequent2
           ]),

         ([testSequent2, testSequent4],
          [testSequent4, testSequent2])
         ]
 
classicalLeftConjunctionTest :: Bool 
classicalLeftConjunctionTest = 
 testCaseTable classicalLeftConjunction classicalLeftConjunctionTestCaseTable 

classicalLeftConjunctionTestVerbose :: IO () 
classicalLeftConjunctionTestVerbose = 
 testCaseTableVerbose classicalLeftConjunction classicalLeftConjunctionTestCaseTable

classicalLeftConjunctionTestCaseTable :: [([Sequent],[Sequent])] 
classicalLeftConjunctionTestCaseTable = 
     let p = makeAtom "p"
         q = makeAtom "q"
         r = makeAtom "r"
         s = makeAtom "s"
         t = makeAtom "t"
         u = makeAtom "u"
         v = makeAtom "v"
         w = makeAtom "w"
         andPQ = (And [p,q])
         andRS = (And [r,s])
         testSequent1 = makeSequent [t, andPQ] [u]
         testSequent2 = makeSequent [v] [w, andPQ]
         testSequent3 = makeSequent [v, andRS] [w]
         resultSequent1 = makeSequent [t,p,q] [u]
         resultSequent2 = makeSequent [v,r,s] [w]
     in [([testSequent1],
         [resultSequent1]),

         ([testSequent1, testSequent2],
          [resultSequent1,
           testSequent2]),

         ([testSequent1, testSequent3],
          [resultSequent1,
           resultSequent2
           ])]

classicalLeftNegationTest :: Bool 
classicalLeftNegationTest = 
 testCaseTable classicalLeftNegation classicalLeftNegationTestCaseTable 

classicalLeftNegationTestVerbose :: IO () 
classicalLeftNegationTestVerbose = 
 testCaseTableVerbose classicalLeftNegation classicalLeftNegationTestCaseTable

classicalLeftNegationTestCaseTable :: [([Sequent],[Sequent])] 
classicalLeftNegationTestCaseTable =
    let p = makeAtom "p"
        q = makeAtom "q"
        r = makeAtom "r"
        s = makeAtom "s"
        notP = Not p
        notQ = Not q
        testSequent1 = makeSequent [r, notP] [s]
        testSequent2 = makeSequent [r]       [s, notP]
        testSequent3 = makeSequent [r, notP, notQ] [s]
        testSequent4 = makeSequent [r, notP] [s, notQ]
        testSequent5 = makeSequent [r, notP] []
        resultSequent1 = makeSequent [r] [s,p]
    in [
     ([testSequent1],
      [resultSequent1]),

    ([testSequent2],
     [testSequent2]),

    ([testSequent3],
     [(makeSequent [r] [s,q,p])]),

    ([testSequent1, testSequent2],
     [resultSequent1, testSequent2]),

    ([testSequent4],
     [(makeSequent [r] [s,notQ,p])]),

    ([testSequent5],
     [(makeSequent [r] [p])])
    ]
                                   
generalizedConjunctionTest :: Bool 
generalizedConjunctionTest = 
 testCaseTable generalizedConjunction generalizedConjunctionTestCaseTable 

generalizedConjunctionTestVerbose :: IO () 
generalizedConjunctionTestVerbose = 
 testCaseTableVerbose generalizedConjunction generalizedConjunctionTestCaseTable

generalizedConjunctionTestCaseTable :: [([Bool],Bool)] 
generalizedConjunctionTestCaseTable =
    [([True,False,False],
      False),
     
     ([False, True, False],
      False),

     ([False, False, True],
      False),

     ([False, True, True],
      False),

     ([True, False, True],
      False),

     ([True, True, False],
      False),

     ([True, True, True],
       True),

     ([False, False, False],
       False)]
    
generalizedDisjunctionTest :: Bool 
generalizedDisjunctionTest = 
 testCaseTable generalizedDisjunction generalizedDisjunctionTestCaseTable 

generalizedDisjunctionTestVerbose :: IO () 
generalizedDisjunctionTestVerbose = 
 testCaseTableVerbose generalizedDisjunction generalizedDisjunctionTestCaseTable

generalizedDisjunctionTestCaseTable :: [([Bool],Bool)] 
generalizedDisjunctionTestCaseTable =      
     [([True,False,False],
      True),
     
     ([False, True, False],
      True),

     ([False, False, True],
      True),

     ([False, True, True],
      True),

     ([True, False, True],
      True),

     ([True, True, False],
      True),

     ([True, True, True],
       True),

     ([False, False, False],
       False)]




cartesianProductTest :: Bool
cartesianProductTest = testCaseTable cartesianProduct cartesianProductTestCaseTable

cartesianProductTestVerbose :: IO ()
cartesianProductTestVerbose = testCaseTableVerbose cartesianProduct cartesianProductTestCaseTable 

cartesianProductTestCaseTable :: [([[Int]],[[Int]])]
cartesianProductTestCaseTable = [
 ([[1,2],[3,4]],
  [[1,3],[2,3],[1,4],[2,4]]),

 ([[1,2,3], [4,5], [6]],
  [[1,4,6], [2,4,6], [3,4,6], [1,5,6], [2,5,6], [3,5,6]]),

 ([[1,2], [3]],
  [[1,3], [2,3]])              

 ] 


--- Because I'm lazy
p = makeAtom "p"
q = makeAtom "q"    
