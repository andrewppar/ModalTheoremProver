import Utilities
import Formula
import Canonicalizer
import Sequent
import Hypersequent
import Prover

type Verbosity = String

main :: IO ()
main = intuitionisticProveTestVerbose



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
           ----proveTest,
           gatherConjunctionsTest,
           addConjunctsTest,
           cartesianProductTest,
           --proveKTest,
           --proveTTest,
           --prove4Test,
           --proveS4Test,
           intuitionisticProveTest, 
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
                        --"proveTest",
                        "gatherConjunctionTest",
                        "addConjunctsTest",
                        "cartesianProductTest" ,
                        --"proveKTest",
                        --"proveTTest",
                        --"prove4Test",
                        --"proveS4Test",
                        "intuitionisticProveTest",
                        "generalizedConjunctionTest",
                        "generalizedDisjunctionTest",
                        "atomicNecessityPTest",
                        "atomicPossibilityPTest"
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
proveTest = testCaseTable prove propositionalProveTestCaseTable

proveTestVerbose :: IO ()
proveTestVerbose = testCaseTableVerbose prove propositionalProveTestCaseTable

propositionalProveTestCaseTable :: [(Formula, ProofTreeStatus)]
propositionalProveTestCaseTable = [ ((Or [(AtomicFormula "p"), (Not (AtomicFormula "p"))]),
                      Proved),

                       ((Not (And [(AtomicFormula "p"), (Not (AtomicFormula "p"))])),
                      Proved),

                       ((And [(Implies (Not (AtomicFormula "a")) (Not (AtomicFormula "c"))), (Or [(Not (Not (AtomicFormula "a"))), (Not (AtomicFormula "c"))])]),
                        CounterExample),

                         ((AtomicFormula "a"),
                          CounterExample),

                         ((equiv (Not (Not (Not (AtomicFormula "a")))) (AtomicFormula "a")),
                          CounterExample),

                         --((equiv (equiv (AtomicFormula "a") (Not (equiv (AtomicFormula "b") (Not (AtomicFormula "c")))))
                           --       (equiv (equiv (AtomicFormula "a") (Not (AtomicFormula "b"))) (Not (AtomicFormula "c")))), Proved) ,


                         --((equiv (AtomicFormula "a") (Or [(AtomicFormula "a"), (Not (AtomicFormula "a"))])),
                         -- CounterExample),

                        ((Implies (AtomicFormula "a") (Or [(AtomicFormula "a"), (Not (AtomicFormula "a"))])),
                                                                                                                              Proved),

                        ((equiv (Implies (Not (Implies (makeAtom "a") (makeAtom "c"))) (makeAtom "b"))
                               (Implies (makeAtom "a") (Implies (Not (makeAtom "b")) (makeAtom "c")))),
                         Proved),


                        ((Or [(Or [(AtomicFormula "a"), (AtomicFormula "b")]), (Not (AtomicFormula "a"))]),
                         Proved),


                       ((Implies (AtomicFormula "a") (AtomicFormula "a")),
                       Proved),

                       ((Implies (And [(makeAtom "a"),
                                       (Implies (makeAtom "a") (makeAtom "b")),
                                       (Implies (makeAtom "b") (makeAtom "c"))])
                                 (makeAtom "c")),
                        Proved),

                       ((equiv (equiv (makeAtom "p") (makeAtom "q")) (equiv (makeAtom "q") (makeAtom "p"))),
                                                                                                                             Proved),

                       ((Implies (And [(Or [(makeAtom "p"), (makeAtom "q")]),
                                       (Implies (makeAtom "p") (Not(makeAtom "q")))])
                                 (Implies (Implies (makeAtom "p") (makeAtom "q"))
                                          (And [(makeAtom "q"), (Not (makeAtom "p"))]))),
                        Proved),


                        ((And [(Implies (Not (Or [(AtomicFormula "a"), (AtomicFormula "b")]))
                                      (And [(Not (AtomicFormula "a")), (Not (AtomicFormula "b"))])),
                             (Implies (And [(Not (AtomicFormula "a")), (Not (AtomicFormula "b"))])

                                      (Not (Or [(AtomicFormula "a"), (AtomicFormula "b")])))]),
                         Proved),

                        ((equiv (And [(AtomicFormula "a"), (AtomicFormula "b")]) (Not (Or [(Not (AtomicFormula "a")), (Not (AtomicFormula "b"))]))),
                         Proved),

                        ((Implies
                          (And
                           [(equiv (makeAtom "TVAI-1") (Implies (And [(makeAtom "A"), (makeAtom "B")]) (makeAtom "C"))),
                            (equiv (makeAtom "TVAI-2") (Implies (And [(makeAtom "A"), (makeAtom "D")]) (makeAtom "C"))),
                            (makeAtom "TVAI-1"),
                            (Implies (makeAtom "D") (makeAtom "B"))])
                           (makeAtom "TVAI-2")),
                         Proved),

                        ((equiv (And [(AtomicFormula "p")]) (AtomicFormula "p")),
                         Proved),
                        ((Implies (Implies (Implies (AtomicFormula "p") (AtomicFormula "q")) (AtomicFormula "p")) (AtomicFormula "p")), Proved)  ,
                     
                      ((Implies (Implies (AtomicFormula "p") (Implies (AtomicFormula "q") (AtomicFormula "p"))) (AtomicFormula "p")), CounterExample) , 

                      ((Implies (Implies (Implies (AtomicFormula "p") (AtomicFormula "q")) (AtomicFormula "p")) (AtomicFormula "p")), Proved)

                     ]

proveKTest :: Bool
proveKTest = testCaseTable prove proveKTestCaseTable

proveKTestVerbose :: IO ()
proveKTestVerbose = testCaseTableVerbose prove proveKTestCaseTable

proveKTestCaseTable :: [(Formula, ProofTreeStatus)]
proveKTestCaseTable = let atomP = makeAtom "p"
                          atomQ = makeAtom "q"
                          nec   = Necessarily
                          pos   = Possibly
                      in [
                       ((nec
                         (Or [(Not atomP), atomP])),
                         Proved),

                       ((Implies
                          (nec (Implies atomP atomQ))
                          (Implies (nec atomP) (nec atomQ))),
                        Proved),

                       ((Not (pos (And [(Not atomP), atomP]))),
                         Proved),

                       ((Not (nec (Not (And [(Not atomP), atomP])))),
                         CounterExample),

                       ((nec
                         (Implies atomP (Or [atomP, atomQ]))),
                        Proved),

                       ((Implies
                         (nec atomP)
                         (nec (Or [atomP, atomQ]))),
                        Proved),

                       ((nec
                         (equiv
                          (Not (nec atomP))
                          (pos (Not atomP)))),
                        Proved),

                       ((nec
                         (equiv
                          (Not (pos atomP))
                          (nec (Not atomP)))),
                        Proved),

                        ((Implies
                          (pos
                           (Implies atomP atomQ))
                          (Implies
                           (nec atomP)
                          (pos atomQ))),
                        Proved),

                       ((Implies
                        (nec atomP)
                        (nec (Or [atomP, atomQ]))),
                        Proved)

                         ]


proveTTest :: Bool
proveTTest =
 testCaseTable prove proveTTestCaseTable

proveTTestVerbose :: IO ()
proveTTestVerbose =
 testCaseTableVerbose prove proveTTestCaseTable

proveTTestCaseTable :: [(Formula, ProofTreeStatus)]
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
        Proved),

       -- 1
       ((Implies
         p
         (pos p)),
        Proved),

       -- 2
       ((Implies
         (nec (nec p))
         p),
        Proved), 

       -- 3
       ((Implies
         (pos
          (Implies
           p
           (nec q)))
         (Implies
          (nec p)
          (pos q))),
       Proved),

       -- 4
       ((Implies
         (nec
          (Implies
           p
           (nec q)))
          (Implies
           (pos p)
           (pos q))),
        Proved),

       -- 5
       ((Implies
        (Implies
         (nec p)
         (pos q))
        (pos
         (Implies
          p
          (pos q)))),
        Proved),

       -- 6
       ((Implies
         (Implies
          (nec p)
          (nec q))
         (pos
          (Implies
           p
           (pos q)))),
        Proved),

       -- 7
       ((Implies
         (nec (nec p))
         (nec p)),
        Proved),

       -- 8
       ((Implies
         (nec p)
         (pos p)),
        Proved)


      ]

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

prove4Test :: Bool
prove4Test =
 testCaseTable prove prove4TestCaseTable

-- It's awesome that this is failing. The reason that it's failing is because we are too eagerly applying propositional rules. When we enforce that we have to weaken and then apply modal rules, we end up making wewakening worthless. The point of weaknening is that we can wait a little while  before collapsing any empty sequents. We need the computer to do some waiting.


prove4TestVerbose :: IO ()
prove4TestVerbose =
 testCaseTableVerbose prove prove4TestCaseTable

prove4TestCaseTable :: [(Formula, ProofTreeStatus)]
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
        Proved),

       ((Implies
         (nec p)
         (nec (nec (nec p)))),
        Proved),

      ((Implies
        (pos (pos p))
        (pos p)),
       Proved),

       ((Implies
         (pos (pos (pos p)))
         (pos p)),
        Proved),

 -- 5 Axiom

     ((Implies
        (pos p)
        (nec 
         (pos p))), CounterExample) , 

-- B Axiom 
  
    ((Implies
       p 
       (nec 
         (pos p))), CounterExample) , 

    ((Implies 
       p
       p), Proved), 
    
    ((Implies (nec p) (nec (nec (nec (nec (nec (nec (nec p)))))))), Proved), 

    ((nec (Implies (nec p) (nec (nec p)))), Proved)
       ]

proveS4Test :: Bool
proveS4Test =
 testCaseTable prove proveS4TestCaseTable


proveS4TestVerbose :: IO ()
proveS4TestVerbose =
 testCaseTableVerbose prove proveS4TestCaseTable

proveS4TestCaseTable :: [(Formula, ProofTreeStatus)]
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
        Proved),

       -- 1
       ((Implies
         p
         (pos p)),
        Proved),

       -- 2
       ((Implies
         (nec (nec p))
         p),
        Proved),

       -- 3
       ((Implies
         (nec p)
         (nec (nec p))),
         Proved),

       -- 4
       ((Implies
         (pos
          (Implies
           p
           (nec q)))
         (Implies
          (nec p)
          (pos q))),
        Proved),

       -- 5
       ((Implies
         (nec
          (Implies
           p
           (nec q)))
          (Implies
           (pos p)
           (pos q))),
        Proved),

       -- 6
       ((Implies
        (Implies
         (nec p)
         (pos q))
        (pos
         (Implies
          p
          (pos q)))),
        Proved),

       -- 7
       ((Implies
         (Implies
          (nec p)
          (nec q))
         (pos
          (Implies
           p
           (pos q)))),
        Proved),

       -- 8
       ((Implies
         (nec (nec p))
         (nec p)),
        Proved),

       -- 9
       ((Implies
         (nec p)
         (pos p)), 
        Proved),

       ((Implies
         (nec p)
         (nec (nec p))),
        Proved),

       ((Implies
         (nec p)
         (nec (nec (nec p)))),
        Proved),

      ((Implies
        (pos (pos p))
        (pos p)),
       Proved),

       ((Implies
         (pos (pos (pos p)))
         (pos p)),
        Proved),

       ((Implies
         (nec p)
         (nec (pos (nec p)))),
        Proved),

      ((Implies
        (nec p)
        p),
       Proved),

       ((Implies
         (nec
          (Implies p
           (nec q)))
         (Implies
          (pos p )
          (pos q ))),
        Proved),

 -- 5 Axiom

     ((Implies
        (pos p)
        (nec 
         (pos p))), CounterExample) , 

-- B Axiom 
  
    ((Implies
       p 
       (nec 
         (pos p))), CounterExample) , 

    ((Implies 
       p
       p), Proved), 
    
    ((Implies (nec p) (nec (nec (nec (nec (nec (nec (nec p)))))))), Proved), 

    ((nec (Implies (nec p) (nec (nec p)))), Proved)
       ]

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
  , ((Implies p (Not (Not p))), Proved) -- FAILING
  , ((Not (And [p, (Not p)])), Proved)
  , ((Necessarily p), CounterExample)
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
  [[1,3],[1,4],[2,3],[2,4]]),

 ([[1,2,3], [4,5], [6]],
 [[1,4,6],[1,5,6],[2,4,6],[2,5,6],[3,4,6],[3,5,6]]),

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
