module Formula
    (Formula (..)
    , equiv
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
    , atomicNecessityP) where

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




-- Uttlities

joinStrings :: String -> [String] -> String
joinStrings _ [] = " "
joinStrings stringToInsert (x:xs) = x ++ (foldl (\string accumulator -> string ++ stringToInsert ++  accumulator) "" xs)
