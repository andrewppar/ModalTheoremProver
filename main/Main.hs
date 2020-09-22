import Utilities
import Formula
import Canonicalizer
import Sequent
import Hypersequent
import DepthFirstProver
import Data.Maybe

main :: IO ()
main = 
    do 
      system  <- getSystem 
      formula <- getFormula 
      case system of 
        K -> putStrLn . show . proveK $ formula
        T -> putStrLn . show . proveT $ formula 
        Four -> putStrLn . show . prove4 $ formula 
        SFour -> putStrLn . show . proveS4 $ formula 
        Intuitionism -> putStrLn . show . proveIntuitionism $ formula
      main
      

getSystem :: IO(System) 
getSystem = do 
   putStrLn "Which System would you like to use:" 
   putStrLn "" 
   putStrLn "[1] System K" 
   putStrLn "[2] System T" 
   putStrLn "[3] System 4" 
   putStrLn "[4] System S4"
   putStrLn "[5] Intuitionistic Logic"
   putStrLn ""
   system <- getLine 
   case system of 
      "1" -> return K 
      "2" -> return T
      "3" -> return Four
      "4" -> return SFour 
      "5" -> return Intuitionism
      otherwise -> 
         do
          putStrLn "Not a supported System"  
          getSystem

      
getFormula :: IO(Formula)      
getFormula = do 
  putStrLn "Enter a Formula: " 
  formulaString <- getLine
  let formula = parseFormula formulaString
   in  if formula /= Nothing
          then return . Data.Maybe.fromJust $ formula  
        else do 
          putStrLn $ formulaString ++ " is not a parsable into a formula." 
--" Enter 'h' for a specification of parsable strings."  
          getFormula
