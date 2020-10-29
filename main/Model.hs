module Model
  (Model (..)
  , satisfies
  , buildModelFromHypersequent
  , hypersequentSatisfies
  , getCounterExample
  , transitivelyCloseRelations 
  , createWorldMatrix
  , transitivelyCloseMatrix 
  , expandMatrixOneStep 
  , makeWorldsAndRelations 
  )
    where
import Formula
import Sequent
import Hypersequent
import Utilities
import Data.Maybe
import qualified Data.Map as Map

---------------
---- Models ---
---------------

data Model = Model {worlds :: [PossibleWorld]
                   , relations :: [(PossibleWorld, PossibleWorld)]
                   } deriving (Eq)

instance Show Model where 
  show model = 
    let ws = mapAppend (\w -> show w ++ "\n") . worlds $ model
        rs = mapAppend (\r -> show r ++ "\n") . relations $ model
     in "Worlds: \n " ++ ws ++ "\n" ++ "Relations: \n" ++ rs 
      

data PossibleWorld = PossibleWorld {trueFormulas :: [Formula]
                   , falseFormulas :: [Formula]
                   } deriving (Eq, Ord)

instance Show PossibleWorld where 
  show world = "w |= " ++ (show . trueFormulas $ world) ++ "|/= " ++ (show . falseFormulas $ world)

makeWorld :: [Formula] -> [Formula] -> PossibleWorld
makeWorld trueFormulas falseFormulas = 
  let trues = (slowRemoveDuplicates trueFormulas)
      falses = (slowRemoveDuplicates falseFormulas)
   in (PossibleWorld  trues falses)

addTrueFormula :: PossibleWorld -> Formula -> PossibleWorld 
addTrueFormula (PossibleWorld true false) formula = 
  PossibleWorld (formula:true) false

addFalseFormula :: PossibleWorld -> Formula -> PossibleWorld
addFalseFormula (PossibleWorld true false) formula = 
  PossibleWorld true (formula:false)

getRelatedWorlds :: Model -> PossibleWorld -> [PossibleWorld]
getRelatedWorlds (Model worlds relations) world = 
  map snd . filter (\(worldOne, worldTwo)  -> worldOne == world) $ relations

makeWorldFromSequent :: Sequent -> PossibleWorld 
makeWorldFromSequent (Sequent negs poss) = 
  makeWorld negs poss

hypersequentSatisfies :: Formula -> Hypersequent -> Bool 
hypersequentSatisfies formula hyper@(World seq hypers) = 
  let world = makeWorldFromSequent seq 
      model = buildModelFromHypersequent hyper
   in satisfies formula model world

getCounterExample :: Formula -> [Hypersequent] -> Maybe Model
getCounterExample formula [] = Nothing
getCounterExample formula (h@(World seq moreHypers):hypers) = 
  let model = buildModelFromHypersequent h
      world = makeWorldFromSequent seq 
   in if satisfies (Not formula) model world
         then (Just model)
      else getCounterExample formula hypers


satisfies :: Formula -> Model -> PossibleWorld -> Bool
satisfies form model world = 
  if world `elem` (worlds model)
     then let (_, satisfactionValue) = satisfiesInternal form model world
           in satisfactionValue
     else False

satisfiesInternal :: Formula -> Model -> PossibleWorld -> (Model, Bool)
-- TODO: There are probably  some good  abstractions  to  be made
-- in the quantified parts of this
satisfiesInternal form@(AtomicFormula string) model world = 
  let (foundAnswer, modelBoolPair) = checkFormulaInWorld form model world
   in if foundAnswer 
         then modelBoolPair 
         else ((addConsistentFormula (AtomicFormula string) model world True), True)
satisfiesInternal (Not (AtomicFormula string)) model world = 
  if (AtomicFormula string) `elem` (falseFormulas world)
     then (model, True)
     else ((addConsistentFormula (AtomicFormula string) model world False), True)
satisfiesInternal (Not form) model world = 
  let (updatedModel, satisfiedNegatum) = satisfiesInternal form model world
   in (updatedModel, (not satisfiedNegatum))
satisfiesInternal (And forms) model world = 
  satisfiesJunctionInternal forms model world True 
satisfiesInternal (Or forms) model world = 
  satisfiesJunctionInternal forms model world False
-- These two cases are messy, whether or not we can show
-- that a model satisfies a formula depends on the order that we 
-- evaluate that question for related worlds
satisfiesInternal (Necessarily form) model world = 
  let relatedWorlds = getRelatedWorlds model world 
   in satisfiesModalInternal form model relatedWorlds True
satisfiesInternal (Possibly form) model world =
  let relatedWorlds = getRelatedWorlds model world
   in satisfiesModalInternal form model relatedWorlds False

satisfiesJunctionInternal ::  [Formula] -> Model -> PossibleWorld -> Bool -> (Model, Bool)
satisfiesJunctionInternal [] model _ startBool =  (model, startBool)
satisfiesJunctionInternal  (x:xs) model world startBool = 
  let (updatedModel, result) = satisfiesInternal x model  world
   in if result /= startBool 
         then (updatedModel, result)
         else satisfiesJunctionInternal xs updatedModel world startBool

satisfiesModalInternal :: Formula -> Model -> [PossibleWorld] -> Bool -> (Model, Bool)
satisfiesModalInternal _ model [] startBool = (model, startBool)
satisfiesModalInternal form model (world:worlds) startBool = 
  let (updatedModel, result) = satisfiesInternal  form model world
   in if  result /= startBool 
         then (updatedModel, result)
         else  satisfiesModalInternal form model worlds startBool

checkFormulaInWorld :: Formula -> Model -> PossibleWorld -> (Bool, (Model, Bool))
checkFormulaInWorld form model world = 
  if  form `elem` (trueFormulas world)
     then (True, (model, True))
     else if form `elem` (falseFormulas world)
          then (True, (model, False))
          else (False, (model, False))

addConsistentFormula :: Formula -> Model -> PossibleWorld -> Bool -> Model
addConsistentFormula form model world position = 
  let modelWorlds = worlds model
   in if not (world `elem` modelWorlds) -- #inefficient we should get the matching world while we check
         then model
      else let newWorld = case position of 
                              True  -> addTrueFormula world form
                              False -> addFalseFormula world form
            in replaceWorldInModel model world newWorld 

replaceWorldInModel :: Model -> PossibleWorld -> PossibleWorld -> Model
replaceWorldInModel (Model worlds relations) oldWorld newWorld = 
  let newWorlds = replaceWorldInList worlds oldWorld newWorld
      newRelations = replaceWorldInRelations relations oldWorld newWorld
   in Model newWorlds newRelations

replaceWorldInList :: [PossibleWorld] -> PossibleWorld -> PossibleWorld -> [PossibleWorld]
replaceWorldInList [] _ _ = []  
replaceWorldInList (x:xs) old new = 
  let recursiveCase = replaceWorldInList xs old new
   in  if x == old 
          then (new:recursiveCase)
          else (x:recursiveCase)

replaceWorldInRelations :: [(PossibleWorld, PossibleWorld)] -> PossibleWorld -> PossibleWorld -> [(PossibleWorld, PossibleWorld)]
replaceWorldInRelations xs old new = 
  foldr (\r@(rel, relum) acc -> 
    if rel == old && relum == old
       then ((new, new):acc)
       else if rel == old 
               then ((new, relum):acc)
               else if relum == old
                       then ((rel, new):acc)
                       else r:acc) [] xs
  

buildModelFromHypersequent :: Hypersequent -> Model
buildModelFromHypersequent hypersequent = 
  let (worlds, relations) = makeWorldsAndRelations hypersequent
      resultRelations = transitivelyCloseRelations worlds relations
   in Model worlds resultRelations

makeWorldsAndRelations :: Hypersequent -> ([PossibleWorld], [(PossibleWorld, PossibleWorld)])
makeWorldsAndRelations (World seq hypers) = 
  let newWorld = makeWorldFromSequent seq
      (internalWorlds, internalRelations)  = 
        joinModelPairs . map (makeWorldsAndRelationsInternal newWorld) $ hypers
   in ((newWorld:internalWorlds), ((newWorld,newWorld):internalRelations))

makeWorldsAndRelationsInternal :: PossibleWorld -> Hypersequent -> ([PossibleWorld],  [(PossibleWorld, PossibleWorld)])
makeWorldsAndRelationsInternal world (World seq hypers) = 
  let newWorld = makeWorldFromSequent seq 
      newRelations = [ (world, newWorld) 
                     , (newWorld, newWorld)]
      (recursiveWorlds, recursiveRelations) = 
        joinModelPairs  . map (makeWorldsAndRelationsInternal newWorld) $ hypers
      resultWorlds = [newWorld] ++  recursiveWorlds
      resultRelations = 
        slowRemoveDuplicates $ newRelations ++ recursiveRelations 
   in  (resultWorlds, resultRelations) 

joinModelPairs :: [([PossibleWorld], [(PossibleWorld, PossibleWorld)])] -> ([PossibleWorld], [(PossibleWorld, PossibleWorld)])
joinModelPairs [] = ([], [])
joinModelPairs ((worlds, relations):pairs) = 
  let (recursiveWorlds, recursiveRelations) = joinModelPairs pairs
   in ((worlds ++ recursiveWorlds), (relations ++ recursiveRelations))


transitivelyCloseRelations :: [PossibleWorld] -> [(PossibleWorld, PossibleWorld)] -> [(PossibleWorld, PossibleWorld)]
transitivelyCloseRelations worlds relations = 
  let worldMatrix = createWorldMatrix worlds relations 
      newMatrix = transitivelyCloseMatrix worlds worldMatrix 
   in relationsFromMatrix worlds newMatrix

createWorldMatrix :: [PossibleWorld] -> [(PossibleWorld, PossibleWorld)] -> Map.Map PossibleWorld [PossibleWorld]
createWorldMatrix worlds relations = 
  let matrixPairs = 
        map (\world -> 
          let relatedWorlds = 
                map snd . filter (\(w1, w2) -> w1 == world) $ relations 
           in (world, relatedWorlds)) $  worlds
    in Map.fromList matrixPairs

transitivelyCloseMatrix :: [PossibleWorld] -> Map.Map PossibleWorld [PossibleWorld]  -> Map.Map PossibleWorld [PossibleWorld]
transitivelyCloseMatrix worlds map = 
  let (status, oneStep) = expandMatrixOneStep worlds map
   in case status of  
     True  -> transitivelyCloseMatrix worlds oneStep
     False -> oneStep

relatedWorldsInMatrix :: PossibleWorld ->  Map.Map PossibleWorld  [PossibleWorld]  -> [PossibleWorld]
relatedWorldsInMatrix world map = 
  let maybeLookup = Map.lookup world map
   in case  maybeLookup of  
     Nothing -> []  
     Just xs -> filter (\x -> x /=  world)  xs

expandMatrixOneStep :: [PossibleWorld]  -> Map.Map PossibleWorld [PossibleWorld] -> (Bool, Map.Map PossibleWorld [PossibleWorld])
expandMatrixOneStep worlds map = 
 foldr (\world (updated, newMatrix) -> 
   let relatedWorlds  = relatedWorldsInMatrix world map
    in if emptyListP relatedWorlds
         then (updated, newMatrix)
       else let oneStepWorlds = 
                  slowRemoveDuplicates . 
                  mapAppend (\relatedWorld -> 
                    relatedWorldsInMatrix relatedWorld map) $ relatedWorlds
                newWorlds =
                  filter (\w -> not (w `elem` relatedWorlds)) oneStepWorlds
             in if emptyListP newWorlds 
                   then (updated, newMatrix)
                else (True, (Map.insertWith (++) world newWorlds map)))
  (False, map) worlds

relationsFromMatrix :: [PossibleWorld] -> Map.Map PossibleWorld [PossibleWorld] -> [(PossibleWorld, PossibleWorld)]
relationsFromMatrix worlds matrix = 
  mapAppend (\world -> 
    let relatedWorlds = fromJust . (Map.lookup world) $ matrix 
     in map (\relatum -> (world, relatum)) relatedWorlds) worlds



p = (AtomicFormula "p")
q = (AtomicFormula "q")
np = (Not p)
pandq = (And [p, q])
s1 = makeSequent  [] [p]
s2 = makeSequent [p] [q]
s3  = makeSequent [p] [np, pandq]
s4 = makeSequent [] [np]
h1  = (World s1 [(World s1 [])])
h2 = (World s2 [(World s3 [(World s1 [])]), (World s4 [])])

f = (Or [(Necessarily p), (Necessarily (Possibly (Not p)))])
h = World (makeSequent [] []) [(World (makeSequent [p] [Possibly np]) []), (World  (makeSequent [] [p]) [])]
m = buildModelFromHypersequent h
subs = disjuncts . negatum $ f
rs = getRelatedWorlds m (head (worlds m))
abcd = head rs
