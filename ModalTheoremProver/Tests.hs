import ModalTheoremProver.Utilities
import ModalTheoremProver.Formula
import ModalTheoremProver.Canonicalizer
import ModalTheoremProver.Sequent
import ModalTheoremProver.Hypersequent
import ModalTheoremProver.IntuitionisticTranslator
import ModalTheoremProver.Prover
import Data.Maybe

type Verbosity = String

main :: IO ()
main = intuitionisticProveTestVerbose



testCase :: (Eq b) => (a -> b) -> a -> b -> Bool
testCase f input output = (f input) == output

--showTestCase :: (Show a) => (Show b) => (Eq b) => (a -> b) -> a -> b -> (Bool, IO ())
showTestCase function input output = let result = function input
                                         bool   = result == output
                                     in (bool, do putStrLn ( "Input: " ++ (show input) ++ "\n" ++ (show ((canonicalizeFormula . fromJust . intuitionisticTranslate) $ input)))
                                                  putStrLn ("Desired: " ++ (show output))
                                                  if bool
                                                  then putStrLn "Success\n"
                                                  else do putStrLn "Failure"
                                                          putStrLn ("Actual: " ++
                                                                    (show result) ++
                                                                    "\n"))

testCaseTable :: (Eq b) => (a -> b) -> [(a,b)] -> Bool
testCaseTable function inputOutputPairs = (foldr (\(input,output) success -> if (testCase function input output) then (success && True) else (success && False))) True inputOutputPairs

--testCaseTableVerbose :: (Eq b, Show a, Show b) => (a -> b) -> [(a,b)] -> IO ()
testCaseTableVerbose function inputOutputPairs =
    let results = (map (\(input,output) -> showTestCase function input output) inputOutputPairs)
    in do sequence_ . map snd $ results
          putStrLn $ "\nOverall Result: " ++
                   if (generalizedConjunction . map fst) results
                   then "Success\n"
                   else let failureCount = 
                              length . filter (\x  -> not  x) . map fst $ results
                            total = length . map fst $ results
                         in "[" ++ (show failureCount) ++ "/" ++ (show total) ++ "] Failures"
 


intuitionisticProveTest :: Bool 
intuitionisticProveTest = 
  testCaseTable prove intuitionisticProveTestCaseTable

intuitionisticProveTestVerbose :: IO()
intuitionisticProveTestVerbose = 
  testCaseTableVerbose prove intuitionisticProveTestCaseTable

intuitionisticProveTestCaseTable :: [(Formula, ProofTreeStatus)]
intuitionisticProveTestCaseTable =  
  [
    ((Or [p, (Not p)]), CounterExample)
  , ((Implies (Implies (Implies p q) p) p), CounterExample)
  , ((Not (Not (Or [p, (Not p)]))), Proved)
  , ((Implies (Not (Not p)) p), CounterExample)
  , ((Implies p (Not (Not p))), Proved) 
  , ((Not (And [p, (Not p)])), Proved) 
  , ((And [(Implies (Not p) (Not q))
           , (Or [(Not (Not p)), (Not q)])]), CounterExample)
  , (p, CounterExample) 
  , ((equiv (Not (Not (Not p))) p), CounterExample)
  , ((Implies p (Or [p, (Not p)])), Proved)
  , ((Or [(Or [p, q]), (Not p)]), CounterExample)
  , ((Implies p p), Proved)
  , ((Implies (And [p 
                    , (Implies p q)
                    , (Implies q r)])
              r), Proved)
  , ((equiv (equiv p q) (equiv q p)), Proved)
  , ((Implies (And [(Or [p, q]), (Implies p (Not q)), (Implies p q)])
              (And [q, (Not p)])), Proved)
  , ((And [(Implies (Not (Or [p, q])) (And [(Not p), (Not q)]))
          ,(Implies (And [(Not p), (Not q)]) (Not (Or [p, q])))]), Proved)
  , ((Implies (Not (Not p)) p), CounterExample)
  , ((Implies p (Not (Not p))), Proved)
  , ((Implies (Or [(Not p), (Not q)]) (Not (And [p, q]))), Proved)
  , ((Not (Not (Implies (equiv (Not p) (Not p)) (Not q)))), CounterExample)
  , ((Not (Not (Implies (Not (equiv (Not p) (Not p))) (Not q)))), Proved)
  , ((Not (Not (Implies (Not (Implies p  p)) (Not q)))), Proved)
--  , ((Not (Not (Or [(Not (Implies (Not p) (Not (Not p)))), p]))), Proved)
-- 
--  , ((Not (Not (Or [(Not (equiv p (Not p))), (Not (Not p))]))), Proved)
  , ((equiv (And [(AtomicFormula "a"), (AtomicFormula "b")]) 
            (Not 
              (Or [ (Not (AtomicFormula "a"))
                   ,(Not (AtomicFormula "b"))]))), CounterExample)
--
--                        ((Implies
--                          (And
--                           [(equiv (makeAtom "TVAI-1") (Implies (And [(makeAtom "A"), (makeAtom "B")]) (makeAtom "C"))),
--                            (equiv (makeAtom "TVAI-2") (Implies (And [(makeAtom "A"), (makeAtom "D")]) (makeAtom "C"))),
--                            (makeAtom "TVAI-1"),
--                            (Implies (makeAtom "D") (makeAtom "B"))])
--                           (makeAtom "TVAI-2")),
--                         Proved),
--
  , ((equiv (And [(AtomicFormula "p")]) (AtomicFormula "p")) , Proved)
  , (p, CounterExample)
  , ((Not p),  CounterExample)
  , ((Implies (Implies (Not (Implies p q)) r)
              (Implies p (Implies (Not r) q))), CounterExample)

  ] 

p = makeAtom "p" 
q = makeAtom "q"
r = makeAtom "r"
