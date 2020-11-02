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
     then let (updatedModel, value) = satisfiesInternal form model world 
           in case value of 
             Just value -> value 
             Nothing -> False 
     else False

satisfiesInternal :: Formula -> Model -> PossibleWorld -> (Model, Maybe Bool)
-- TODO: There are probably  some good  abstractions  to  be made
-- in the quantified parts of this
satisfiesInternal form@(AtomicFormula string) model world = 
  if form `elem` (trueFormulas world)
     then (model, Just True)
     else if form `elem` (falseFormulas world)
             then (model, Just False)
             else addFormulaToModelAtWorld form model world True
satisfiesInternal (Not (AtomicFormula string)) model world =
 if (AtomicFormula  string) `elem` (trueFormulas world) 
    then (model, Just False)
    else if (AtomicFormula string)  `elem` (falseFormulas world)
         then (model, Just True)
         else addFormulaToModelAtWorld (AtomicFormula string) model world False
satisfiesInternal (Not form) model world = 
  let (newModel, recursiveValue) = satisfiesInternal form model world
      result = case recursiveValue of 
                   Just True  -> (newModel, Just False)
                   Just False -> (newModel, Just True)
                   Nothing    -> (newModel, Nothing)
   in result 
satisfiesInternal (And forms) model world = 
  satisfiesJunctionInternal forms model world True
satisfiesInternal (Or forms) model world = 
  satisfiesJunctionInternal forms model world False 

satisfiesInternal (Necessarily form) model world = 
  let relatedWorlds = getRelatedWorlds model world
   in satisfiesModalInternal form model relatedWorlds True
satisfiesInternal (Possibly form) model world =
  let relatedWorlds = getRelatedWorlds model world
   in satisfiesModalInternal form model relatedWorlds False 

addFormulaToModelAtWorld :: Formula -> Model -> PossibleWorld -> Bool -> (Model, Maybe Bool)
addFormulaToModelAtWorld form model old@(PossibleWorld true false) position = 
  let newWorld = (case  position of 
                     True  -> (PossibleWorld (form:true) false)
                     False -> (PossibleWorld true (form:false)))
      newModel = replaceWorldInModel model old newWorld 
   in (newModel, Just position)
        
replaceWorldInModel :: Model -> PossibleWorld -> PossibleWorld -> Model
replaceWorldInModel model old new = 
  let newWorlds = replaceWorldInWorlds (worlds model) old new
      newRelations = replaceWorldInRelations (relations model) old new
   in (Model newWorlds newRelations)

replaceWorldInWorlds ::  [PossibleWorld] -> PossibleWorld -> PossibleWorld -> [PossibleWorld]
replaceWorldInWorlds [] _ _  = []
replaceWorldInWorlds (world:worlds) old new = 
  if world == old
     then (new:(replaceWorldInWorlds worlds old new))
     else (world:(replaceWorldInWorlds worlds old new))

replaceWorldInRelations :: [(PossibleWorld, PossibleWorld)] -> PossibleWorld -> PossibleWorld -> [(PossibleWorld, PossibleWorld)]
replaceWorldInRelations []  _ _ = []
replaceWorldInRelations ((relator, related):relations) old new  
  | relator == old && related == old = 
    ((new, new):replaceWorldInRelations relations old new)
  | relator == old = 
    ((new, related):replaceWorldInRelations relations old new)
  | related == old = 
    ((relator, new): replaceWorldInRelations relations old new)
  | otherwise = 
    ((relator,related): replaceWorldInRelations relations old new)

satisfiesJunctionInternal :: [Formula] -> Model -> PossibleWorld -> Bool -> (Model, Maybe Bool)
satisfiesJunctionInternal [] model _ startingValue =
  (model, Just startingValue)
satisfiesJunctionInternal (x:xs) model world startingValue = 
  let (updatedModel, recursiveValue) = satisfiesInternal x model world
   in case recursiveValue of 
     Just value ->
       if value /= startingValue
          then (updatedModel, Just value)
          else satisfiesJunctionInternal xs model world startingValue
     Nothing -> (updatedModel, Nothing)

satisfiesModalInternal :: Formula -> Model -> [PossibleWorld] -> Bool -> (Model, Maybe Bool)
satisfiesModalInternal _ model [] startingValue = 
  (model, Just startingValue)
satisfiesModalInternal form model (world:worlds) startingValue = 
  let (updatedModel, recursiveValue) = satisfiesInternal form model world
   in case recursiveValue of 
     Just value -> 
       if value /= startingValue 
          then (updatedModel, Just value)
          else satisfiesModalInternal form model worlds startingValue 
     Nothing -> (updatedModel, Nothing)


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

f = (Necessarily (Possibly (Or [(Necessarily p), (Necessarily (Possibly (Not p)))])))
--h = World (makeSequent [] []) [(World (makeSequent [p] [Possibly np]) []), (World  (makeSequent [] [p]) [])]
h = World (makeSequent [] [f]) []
m = buildModelFromHypersequent h
subs = disjuncts . negatum $ f
rs = getRelatedWorlds m (head (worlds m))
abcd = head rs
