import Utilities
import Formula
import Canonicalizer
import Sequent
import Hypersequent
import DepthFirstProver

main :: IO ()
main = 
    do 
      system  <- getSystem 
      putStrLn . show $ system
      formula <- getFormula 
      

getSystem :: IO(System) 
getSystem = do 
   putStrLn "Which System would you like to use:" 
   putStrLn "" 
   putStrLn "[1] System K" 
   putStrLn "[2] System T" 
   putStrLn "[3] System 4" 
   putStrLn "[4] System S4"
   putStrLn ""
   system <- getLine 
   case system of 
      "1" -> return K 
      "2" -> return T
      "3" -> return Four
      "4" -> return SFour 
      otherwise -> 
         do
          putStrLn "Not a supported System"  
          getSystem

      
getFormula :: IO(Formula)      
getFromula = do 
  putStrLn "Enter a Formula: " 
  formulaString <- getLine
  if parseAble formulaString
    then return . parseFormula $ formulaString
  else do 
    putStrLn $ formulaString ++ " is not a parseableFormula. "
    getFormula
