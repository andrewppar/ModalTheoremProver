import System.Environment
import ModalTheoremProver.Prover
import ModalTheoremProver.Formula
import Data.Maybe

main :: IO()
main = 
  do 
    args <- getArgs
    parseArgs args

parseArgs :: [String] -> IO()
parseArgs ["-h"] = do 
  putStrLn "Intuitionistic Theorem Prover"
  putStrLn "  -----                ------------       " 
  putStrLn " |:::::|              |:::::::::::::\\     "
  putStrLn " |:::::|              |::::::--::::::\\    " 
  putStrLn " |:::::|              |:::::|   \\:::::\\   " 
  putStrLn " |:::::|              |:::::|   /:::::/   " 
  putStrLn " |::::: ----------    |::::::--::::::/    " 
  putStrLn " |::::::::::::::::|   |:::::::::::::/     "
  putStrLn " |::::::::::::::::|   |:::::::::::::\\     "
  putStrLn " |::::: ----------    |::::::--::::::\\    " 
  putStrLn " |:::::|              |:::::|   \\:::::\\   " 
  putStrLn " |:::::|              |:::::|   /:::::/   " 
  putStrLn " |:::::|              |::::::--::::::/    " 
  putStrLn " |:::::|              |:::::::::::::/     " 
  putStrLn "  -----                ------------       " 
  putStrLn ""
  putStrLn "Usage: " 
  putStrLn "./Main [options] [formula]" 
  putStrLn "Available Options: "
  putStrLn "-h Prints a help menu"
  putStrLn "-f Prints an explanation of how formulas are specified"
  putStrLn "-s FORM  shows the proof or counter-model for FORM"
  putStrLn "" 
  putStrLn ""
parseArgs ["-f"] = do
  putStrLn "Formulas are written in prefix notation with parentheses "
  putStrLn "surrounding each one. Formally, if O is an connective and "
  putStrLn "ARGS are arguments of the correct type, then (O ARGS) is "
  putStrLn "a well-formed formula. The supported connective and "
  putStrLn "argument combinations are listed below: "
  putStrLn "" 
  putStrLn "AtomicFormula: Takes a single string as argument." 
  putStrLn "    Example: (AtomicFormula \"p\") "
  putStrLn "Not: Takes a formula as an argument. " 
  putStrLn "    Example: (Not (AtomicFormula \"p\"))"
  putStrLn "And: Takes a list of formulas as an argument. "
  putStrLn "    Example: (And [(AtomicFormula \"p\"), (Not (AtomicFormula \"p\"))])"
  putStrLn "Or: Takes a list of formulas as an argument. "
  putStrLn "    Example: (Or [(AtomicFormula \"p\"), (Not (AtomicFormula \"p\"))])"
  putStrLn "Implies: Takes two formulas as arguments. "
  putStrLn "    Example: (Implies (AtomicFormula \"p\") (AtomicFormula \"p\"))"
  putStrLn "Equivalent: Takes two formulas as arguments. "
  putStrLn "    Example: (Equivalent (AtomicFormula \"p\") (AtomicFormula \"p\"))"
  putStrLn ""
  putStrLn "NOTE:" 
  putStrLn "In many shells the strings for an atomic formula will have to" 
  putStrLn "be escaped. It is recommended that when passing arguments directly"
  putStrLn "to the command line single quotes are used to specify the formula"
  putStrLn "e.g. ./ModalTheoremProver/Main  \'(AtomicFormula \"p\")\'"
parseArgs ["-s", formula] = 
  let parsedFormula = parseFormula formula
   in if parsedFormula == Nothing
         then do putStrLn (formula ++ " is not a well-formed formula")
         else do putStrLn . show . showProof . fromJust $ parsedFormula
parseArgs [formula] =
  let parsedFormula = parseFormula formula
   in if parsedFormula == Nothing
         then do putStrLn (formula ++ " is not a well-formed formula")
         else do if  (show . prove . fromJust $ parsedFormula) == "Proved"
                     then putStrLn $ " is an intuitionistic tautology"
                     else putStrLn $ " is not an intuitionistic tautology"
