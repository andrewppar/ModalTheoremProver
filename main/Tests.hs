module Tests
    (runAllTests
    , runAllTestsVerbose)
    where

{-| Testing |-}

import Utilities
import Formula
import Canonicalizer
import Sequent
import Hypersequent
import DepthFirstProver

type Verbosity = String

main :: IO ()
main = runAllTestsVerbose



testCase :: (Eq b) => (a -> b) -> a -> b -> Bool
testCase f input output = (f input) == output

showTestCase :: (Show a) => (Show b) => (Eq b) => (a -> b) -> a -> b -> (Bool, IO ())
showTestCase function input output = let result = function input
                                         bool   = result == output
                                     in (bool, do putStrLn ( "Input: " ++ (show input))
                                                  putStrLn ("Desired: " ++ (show output))
                                                  if bool
                                                  then putStrLn "Success\n"
                                                  else do putStrLn "Failure"
                                                          putStrLn ("Actual: " ++
                                                                    (show result) ++
                                                                    "\n"))

testCaseTable :: (Eq b) => (a -> b) -> [(a,b)] -> Bool
testCaseTable function inputOutputPairs = (foldr (\(input,output) success -> if (testCase function input output) then (success && True) else (success && False))) True inputOutputPairs

testCaseTableVerbose :: (Eq b, Show a, Show b) => (a -> b) -> [(a,b)] -> IO ()
testCaseTableVerbose function inputOutputPairs =
    let results = (map (\(input,output) -> showTestCase function input output) inputOutputPairs)
    in do sequence_ . map snd $ results
          putStrLn $ "\nOverall Result: " ++
                   if (generalizedConjunction . map fst) results
                   then "Success\n"
                   else "Failure\n"


---------------- Run All Tests
allTests :: [Bool]
allTests = [canonicalizerTest,
           formulaSetsEqualPTest, 
           cleanFormulaStringTest,
           parseFormulaTest, 
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
           contractRootNodeTest,
           contractLevel1NodesTest,
           proveTTest,
           weakenLevel1NodesTest,
           weakenLevel2NodesTest,
           prove4Test,
           proveS4Test,
           generalizedConjunctionTest,
           generalizedDisjunctionTest,
           atomicNecessityPTest,
           atomicPossibilityPTest
           ]


allTestsWithName :: [(String,Bool)]
allTestsWithName = zip ["canonicalierTest",
                        "formulaSetsEqualPTest", 
                        "cleanFormulaStringTest",
                        "parseFormulaTest", 
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
                        "contractRootNodeTest",
                        "contractLevel1NodesTest",
                        "proveTTest",
                        "weakenLevel1NodesTest",
                        "weakenLevel2NodesTest",
                        "prove4Test",
                        "proveS4Test",
                        "generalizedConjunctionTest",
                        "generalizedDisjunctionTest",
                        "atomicNecessityPTest",
                        "aotmicPossibilityPTest"
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
                       putStrLn $ "Overall Result: " ++ if finalResult
                                                        then "Success!!\n"
                                                        else "Failure\n"




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

cleanFormulaStringTest :: Bool 
cleanFormulaStringTest = 
  testCaseTable cleanFormulaString cleanFormulaStringTestCaseTable 

cleanFormulaStringTestVerbose :: IO ()
cleanFormulaStringTestVerbose =
  testCaseTableVerbose cleanFormulaString cleanFormulaStringTestCaseTable

cleanFormulaStringTestCaseTable :: [(String, String)]
cleanFormulaStringTestCaseTable = [("  a  ", "a")
                                  , (" ( a b )", "(a b)")
                                  , ("(   a (b cd) )", "(a (b cd))")
                                  , (" ( ( a b) )", "((a b))")
                                  , (" ( [a, b ,  c ] )", "([a, b , c])")
                                ]

getListItemsTest :: Bool 
getListItemsTest = 
  testCaseTable getListItems getListItemsTestCaseTable

getListItemsTestVerbose :: IO ()
getListItemsTestVerbose = 
  testCaseTableVerbose getListItems getListItemsTestCaseTable

getListItemsTestCaseTable :: [(String, [String])] 
getListItemsTestCaseTable = [ ("[a, b]", ["a", "b"])
                            , ("[(a, b), c]", ["(a, b)", "c"])
                            , ("[ a , a , b, (c, [d, e])]"
                              , ["a", "a", "b", "(c, [d, e])"])
                            ]

parseFormulaTest :: Bool
parseFormulaTest = 
  testCaseTable parseFormula parseFormulaTestCaseTable

parseFormulaTestVerbose :: IO ()
parseFormulaTestVerbose = 
  testCaseTableVerbose parseFormula parseFormulaTestCaseTable 

parseFormulaTestCaseTable :: [(String, Maybe Formula)]
parseFormulaTestCaseTable = [ ("", Nothing)
                            , (")", Nothing)
                            , ("(a)", Nothing)
                            , ("(AtomicFormula p)", Just (AtomicFormula "p"))
                            , ("   (  Atomic Formula pq )", Nothing)
                            , ("   ( AtomicFormula p q)", Nothing)
                            , ("  ( AtomicFormula p1 )", Just (AtomicFormula "p1"))
                            , (" ( And [(AtomicFormula p1)])"
                              , Just (And [(AtomicFormula "p1")]))
                            , (" (And p1)", Nothing)
                            , (" (And (AtomicFormula p1))", Nothing)
                            , (" (And [(AtomicFormula p1), (AtomicFormula p2)])"
                              , Just (And [(AtomicFormula "p1") 
                                          ,(AtomicFormula "p2")]))
                            , (" (And [(AtomicFormula p1), (AtomicFormula p2]))", Nothing)
                            , ("Implies p q", Nothing)
                            , ("(Implies (AtomicFormula p) (Not (AtomicFormula q)))"
                              , Just (Implies (AtomicFormula "p") (Not (AtomicFormula "q"))))
                            , ("(Implies (L (Implies (AtomicFormula p) (AtomicFormula q))) (Implies (L (AtomicFormula p)) (L (AtomicFormula q))))" , Just (Implies (Necessarily (Implies (AtomicFormula "p") (AtomicFormula "q"))) (Implies (Necessarily (AtomicFormula "p")) (Necessarily (AtomicFormula "q")))))
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

                         ((equiv (equiv (AtomicFormula "a") (Not (equiv (AtomicFormula "b") (Not (AtomicFormula "c")))))
                                  (equiv (equiv (AtomicFormula "a") (Not (AtomicFormula "b"))) (Not (AtomicFormula "c")))), True) ,


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
                                                                                                                                                        True)  ,
                     
                      ((Implies (Implies (AtomicFormula "p") (Implies (AtomicFormula "q") (AtomicFormula "p"))) (AtomicFormula "p")), False) , 

                      ((Implies (Implies (Implies (AtomicFormula "p") (AtomicFormula "q")) (AtomicFormula "p")) (AtomicFormula "p")), True)

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


proveTTest :: Bool
proveTTest =
 testCaseTable proveT proveTTestCaseTable

proveTTestVerbose :: IO ()
proveTTestVerbose =
 testCaseTableVerbose proveT proveTTestCaseTable

proveTTestCaseTable :: [(Formula,Bool)]
proveTTestCaseTable =
    let p   = makeAtom "p"
        q   = makeAtom "q"
        nec = Necessarily
        pos = Possibly
    in
      [
       -- 0
       ((Implies
         (nec p)
         p),
        True),

       -- 1
       ((Implies
         p
         (pos p)),
        True),

       -- 2
       ((Implies
         (nec (nec p))
         p),
        True),

       -- 3
       ((Implies
         (nec p)
         (nec (nec p))),
         False),

       -- 4
       ((Implies
         (pos
          (Implies
           p
           (nec q)))
         (Implies
          (nec p)
          (pos q))),
        True),

       -- 5
       ((Implies
         (nec
          (Implies
           p
           (nec q)))
          (Implies
           (pos p)
           (pos q))),
        True),

       -- 6
       ((Implies
        (Implies
         (nec p)
         (pos q))
        (pos
         (Implies
          p
          (pos q)))),
        True),

       -- 7
       ((Implies
         (Implies
          (nec p)
          (nec q))
         (pos
          (Implies
           p
           (pos q)))),
        True),

       -- 8
       ((Implies
         (nec (nec p))
         (nec p)),
        True),

       -- 9
       ((Implies
         (nec p)
         (pos p)),
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

contractRootNodeTest :: Bool
contractRootNodeTest =
 testCaseTable contractRootNode contractRootNodeTestCaseTable

contractRootNodeTestVerbose :: IO ()
contractRootNodeTestVerbose =
 testCaseTableVerbose contractRootNode contractRootNodeTestCaseTable

contractRootNodeTestCaseTable :: [(Hypersequent,Hypersequent)]
contractRootNodeTestCaseTable =
     let a = makePositiveSequent p
         b = makePositiveSequent q
         c = makePositiveSequent (Implies p q)
         d = makePositiveSequent (Or [p,q])
         hyperInput = (World a
                       [(World c [BranchEnd]),
                        (World b
                         [(World d [BranchEnd])])])
         hyperResult = (World a
                        [(World a [BranchEnd]),
                         (World c [BranchEnd]),
                         (World b
                          [(World d [BranchEnd])])])
     in [(hyperInput, hyperResult),
         ((World a [BranchEnd]),
          (World a [(World a [BranchEnd])]))]

contractLevel1NodesTest :: Bool
contractLevel1NodesTest =
 testCaseTable contractLevel1Nodes contractLevel1NodesTestCaseTable

contractLevel1NodesTestVerbose :: IO ()
contractLevel1NodesTestVerbose =
 testCaseTableVerbose contractLevel1Nodes contractLevel1NodesTestCaseTable

contractLevel1NodesTestCaseTable :: [(Hypersequent,[Hypersequent])]
contractLevel1NodesTestCaseTable =
      let a = makePositiveSequent p
          b = makePositiveSequent q
          c = makePositiveSequent (Implies p q)
          d = makePositiveSequent (Or [p,q])
          hyperInput = (World a
                        [(World c [BranchEnd]),
                         (World b
                          [(World d [BranchEnd])])])
          hyperResult = [(World a
                          [(World c
                            [(World c [BranchEnd])]),
                           (World b
                            [(World d [BranchEnd])])]),
                         (World a
                          [(World c [BranchEnd]),
                           (World b
                            [(World b [BranchEnd]),
                             (World d [BranchEnd])])])]
      in [(hyperInput, hyperResult),

          ((World a
           [(World b [BranchEnd]), (World c [BranchEnd]), (World d [BranchEnd])]),

           [(World a
           [(World b
             [(World b [BranchEnd])]),
            (World c
             [BranchEnd]),
            (World d
             [BranchEnd])]),
           (World a
           [(World b
             [BranchEnd]),
            (World c
             [(World c [BranchEnd])]),
            (World d
             [BranchEnd])]),
          (World a
           [(World b
             [BranchEnd]),
            (World c
             [BranchEnd]),
            (World d
             [(World d [BranchEnd])])])])
         ]

weakenLevel1NodesTest :: Bool
weakenLevel1NodesTest =
 testCaseTable weakenLevel1Nodes weakenLevel1NodesTestCaseTable

weakenLevel1NodesTestVerbose :: IO ()
weakenLevel1NodesTestVerbose =
 testCaseTableVerbose weakenLevel1Nodes weakenLevel1NodesTestCaseTable

weakenLevel1NodesTestCaseTable :: [(Hypersequent,[Hypersequent])]
weakenLevel1NodesTestCaseTable =
    let a = makePositiveSequent p
        b = makePositiveSequent q
        c = makePositiveSequent (Implies p q)
        d = makePositiveSequent (Or [p,q])
        inputHypersequent = (World a
                                   [(World emptySequent
                                               [(World b [BranchEnd])]),
                                    (World c [BranchEnd])])
   in [(inputHypersequent,
       [inputHypersequent, (World a
              [(World b [BranchEnd]),
               (World c [BranchEnd])])])]

weakenLevel2NodesTest :: Bool
weakenLevel2NodesTest =
 testCaseTable weakenLevel2Nodes weakenLevel2NodesTestCaseTable

weakenLevel2NodesTestVerbose :: IO ()
weakenLevel2NodesTestVerbose =
 testCaseTableVerbose weakenLevel2Nodes weakenLevel2NodesTestCaseTable

weakenLevel2Nodes :: Hypersequent -> [Hypersequent]
weakenLevel2Nodes = weakenLevelNNodes 2

weakenLevel2NodesTestCaseTable :: [(Hypersequent,[Hypersequent])]
weakenLevel2NodesTestCaseTable =
    let a = makePositiveSequent p
        b = makePositiveSequent q
        c = makePositiveSequent (Implies p q)
        d = makePositiveSequent (Or [p,q])
        hyperInput = (World a
                      [(World emptySequent
                                  [(World emptySequent [(World b [BranchEnd])])]),
                       (World c [BranchEnd])])
    in [(hyperInput,
                       [hyperInput,
                                      (World a [(World emptySequent
                                                           [(World b [BranchEnd])]),
                                                (World c [BranchEnd])])])]


prove4Test :: Bool
prove4Test =
 testCaseTable prove4 prove4TestCaseTable

-- It's awesome that this is failing. The reason that it's failing is because we are too eagerly applying propositional rules. When we enforce that we have to weaken and then apply modal rules, we end up making wewakening worthless. The point of weaknening is that we can wait a little while  before collapsing any empty sequents. We need the computer to do some waiting.


prove4TestVerbose :: IO ()
prove4TestVerbose =
 testCaseTableVerbose prove4 prove4TestCaseTable

prove4TestCaseTable :: [(Formula,Bool)]
prove4TestCaseTable =
    let p   = makeAtom "p"
        q   = makeAtom "q"
        nec = Necessarily
        pos = Possibly
    in
      [
       ((Implies
         (nec p)
         (nec (nec p))),
        True),

       ((Implies
         (nec p)
         (nec (nec (nec p)))),
        True),

      ((Implies
        (pos (pos p))
        (pos p)),
       True),

       ((Implies
         (pos (pos (pos p)))
         (pos p)),
        True),

       ((Implies
         (nec p)
         (nec (pos (nec p)))),
        False), -- I think I saw this in Hardegree but there are counterexamples

      ((Implies
        (nec p)
        p),
       False),

       ((Implies
         (nec
          (Implies p
           (nec q)))
         (Implies
          (pos p )
          (pos q ))),
        False),

 -- 5 Axiom

     ((Implies
        (pos p)
        (nec 
         (pos p))), False) , 

-- B Axiom 
  
    ((Implies
       p 
       (nec 
         (pos p))), False) , 

    ((Implies 
       p
       p), True), 
    
    ((Implies (nec p) (nec (nec (nec (nec (nec (nec (nec p)))))))), True), 

    ((nec (Implies (nec p) (nec (nec p)))), True)
       ]

proveS4Test :: Bool
proveS4Test =
 testCaseTable proveS4 proveS4TestCaseTable


proveS4TestVerbose :: IO ()
proveS4TestVerbose =
 testCaseTableVerbose proveS4 proveS4TestCaseTable

proveS4TestCaseTable :: [(Formula,Bool)]
proveS4TestCaseTable =
    let p   = makeAtom "p"
        q   = makeAtom "q"
        nec = Necessarily
        pos = Possibly
    in
 [
 -- 0
       ((Implies
         (nec p)
         p),
        True),

       -- 1
       ((Implies
         p
         (pos p)),
        True),

       -- 2
       ((Implies
         (nec (nec p))
         p),
        True),

       -- 3
       ((Implies
         (nec p)
         (nec (nec p))),
         True),

       -- 4
       ((Implies
         (pos
          (Implies
           p
           (nec q)))
         (Implies
          (nec p)
          (pos q))),
        True),

       -- 5
       ((Implies
         (nec
          (Implies
           p
           (nec q)))
          (Implies
           (pos p)
           (pos q))),
        True),

       -- 6
       ((Implies
        (Implies
         (nec p)
         (pos q))
        (pos
         (Implies
          p
          (pos q)))),
        True),

       -- 7
       ((Implies
         (Implies
          (nec p)
          (nec q))
         (pos
          (Implies
           p
           (pos q)))),
        True),

       -- 8
       ((Implies
         (nec (nec p))
         (nec p)),
        True),

       -- 9
       ((Implies
         (nec p)
         (pos p)),
        True), 




       ((Implies
         (nec p)
         (nec (nec p))),
        True),

       ((Implies
         (nec p)
         (nec (nec (nec p)))),
        True),

      ((Implies
        (pos (pos p))
        (pos p)),
       True),

       ((Implies
         (pos (pos (pos p)))
         (pos p)),
        True),

       ((Implies
         (nec p)
         (nec (pos (nec p)))),
        False), -- I think I saw this in Hardegree but there are counterexamples

      ((Implies
        (nec p)
        p),
       True),

       ((Implies
         (nec
          (Implies p
           (nec q)))
         (Implies
          (pos p )
          (pos q ))),
        True),

 -- 5 Axiom

     ((Implies
        (pos p)
        (nec 
         (pos p))), False) , 

-- B Axiom 
  
    ((Implies
       p 
       (nec 
         (pos p))), False) , 

    ((Implies 
       p
       p), True), 
    
    ((Implies (nec p) (nec (nec (nec (nec (nec (nec (nec p)))))))), True), 

    ((nec (Implies (nec p) (nec (nec p)))), True)
       ]



makeAtomicSequentFromSequentTest :: Bool
makeAtomicSequentFromSequentTest =
 testCaseTable makeAtomicSequentFromSequent makeAtomicSequentFromSequentTestCaseTable

makeAtomicSequentFromSequentTestVerbose :: IO ()
makeAtomicSequentFromSequentTestVerbose =
 testCaseTableVerbose makeAtomicSequentFromSequent makeAtomicSequentFromSequentTestCaseTable

makeAtomicSequentFromSequentTestCaseTable :: [(Sequent,Sequent)]
makeAtomicSequentFromSequentTestCaseTable =
      let a = makeAtom "p"
          b = makeAtom "q"
          c = (Implies p q)
          d = (Or [p,q])
          testSequent1 = (makeSequent [a] [b])
          testSequent2 = (makeSequent [a,c] [b])
          testSequent3 = (makeSequent [c] [b])
          testSequent4 = (makeSequent [a] [d,b])
          testSequent5 = (makeSequent [] [b])
          testSequent6 = (makeSequent [c] [d])
          testSequent7 = emptySequent
          resultSequent1 = testSequent1
          resultSequent2 = (makeSequent [] [b])
          resultSequent3 = emptySequent
      in [(testSequent1, resultSequent1),
          (testSequent2, resultSequent1),
          (testSequent3, resultSequent2),
          (testSequent4, resultSequent1),
          (testSequent5, resultSequent2),
          (testSequent6, resultSequent3),
          (testSequent7, resultSequent3)]


--- Utility Tests

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


atomicNecessityPTest :: Bool
atomicNecessityPTest =
 testCaseTable atomicNecessityP atomicNecessityPTestCaseTable

atomicNecessityPTestVerbose :: IO ()
atomicNecessityPTestVerbose =
 testCaseTableVerbose atomicNecessityP atomicNecessityPTestCaseTable

atomicNecessityPTestCaseTable :: [(Formula,Bool)]
atomicNecessityPTestCaseTable = let p = makeAtom "p"
                                    q = makeAtom "q"
                                    notP = (Not p)
                                    notQ = (Not q)
                                    andPQ = (And [p, q])
                                    necP  = (Necessarily p)
                                    necNotP = (Necessarily (Not p))
                                    necPosP = (Necessarily (Possibly p))
                                    necNecNotP = (nec necNotP)
                                in
                                  [(p, False),
                                   (q, False),
                                   (notP, False),
                                   (notQ, False),
                                   (andPQ, False),
                                   (necP, True),
                                   (necNotP, False),
                                   (necPosP, False),
                                   (necNecNotP, False)]

atomicPossibilityPTest :: Bool
atomicPossibilityPTest =
 testCaseTable atomicPossibilityP atomicPossibilityPTestCaseTable

atomicPossibilityPTestVerbose :: IO ()
atomicPossibilityPTestVerbose =
 testCaseTableVerbose atomicPossibilityP atomicPossibilityPTestCaseTable

atomicPossibilityPTestCaseTable :: [(Formula,Bool)]
atomicPossibilityPTestCaseTable = let p = makeAtom "p"
                                      q = makeAtom "q"
                                      notP = (Not p)
                                      notQ = (Not q)
                                      andPQ = (And [p, q])
                                      posP  = (Possibly p)
                                      posNotP = (Possibly (Not p))
                                      posPosP = (Possibly (Possibly p))
                                      posPosNotP = (pos posNotP)
                                  in
                                    [(p, False),
                                     (q, False),
                                     (notP, False),
                                     (notQ, False),
                                     (andPQ, False),
                                     (posP, True),
                                     (posNotP, False),
                                     (posPosP, False),
                                     (posPosNotP, False)]


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
p   = makeAtom "p"
q   = makeAtom "q"
nec = Necessarily
pos = Possibly
ax  = (Implies
       (nec p)
       (nec (nec  p)))
startingHypersequent = makeStartingHypersequent . canonicalizeFormula $ ax
startingProofTree    = (Node startingHypersequent [Leaf])
