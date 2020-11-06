module Model
  (Model (..)
  , satisfies
  , buildModelFromHypersequent
  , hypersequentSatisfies
  , getCounterExample
  , makeWorldsAndRelations
  )
    where
import Formula
import Sequent
import Hypersequent
import Utilities
import Data.Maybe
import qualified Data.Map as Map
import Debug.Trace

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
                                   , tag ::  String
                   } deriving (Eq, Ord)

instance Show PossibleWorld where
  show world = (tag world) ++ " |= " ++ (show . trueFormulas $ world) ++ "|/= " ++ (show . falseFormulas $ world)

generateNextTag :: String -> String
generateNextTag string = show ((read string :: Int) + 1)


makeWorld :: [Formula] -> [Formula] -> String -> PossibleWorld
makeWorld trueFormulas falseFormulas tag =
  let trues = (slowRemoveDuplicates trueFormulas)
      falses = (slowRemoveDuplicates falseFormulas)
   in (PossibleWorld trues falses tag)

addTrueFormula :: PossibleWorld -> Formula -> PossibleWorld
addTrueFormula (PossibleWorld true false tag) formula =
  PossibleWorld (formula:true) false tag

addFalseFormula :: PossibleWorld -> Formula -> PossibleWorld
addFalseFormula (PossibleWorld true false tag) formula =
  PossibleWorld true (formula:false) tag

getRelatedWorlds :: Model -> PossibleWorld -> [PossibleWorld]
getRelatedWorlds (Model worlds relations) =
  getRelatedWorldsInternal [] [] relations

getRelatedWorldsInternal :: [PossibleWorld] -> [PossibleWorld] -> [(PossibleWorld, PossibleWorld)] -> PossibleWorld -> [PossibleWorld]
getRelatedWorldsInternal accumulator visitedWorlds relations world =
  let newVisitedWorlds = (world:visitedWorlds)
      oneStepRelated =
        foldr (\(relator, relatum) acc ->
          if relator == world && relatum /= world && not (relatum `elem` visitedWorlds)
             then (relatum:acc)
             else acc) [] relations
      recursiveResults = mapAppend (getRelatedWorldsInternal accumulator  newVisitedWorlds relations) oneStepRelated
   in world:recursiveResults


makeWorldFromSequent :: Sequent -> String -> PossibleWorld
makeWorldFromSequent (Sequent negs poss) tag =
  makeWorld negs poss tag
    where atoms = filter (\form -> atomicFormulaP form)

hypersequentSatisfies :: Formula -> Hypersequent -> Bool
hypersequentSatisfies formula hyper@(World seq hypers) =
  let world = makeWorldFromSequent seq "0"
      model = buildModelFromHypersequent hyper "0"
   in satisfies formula model world

getCounterExample :: Formula -> [Hypersequent] -> Maybe Model
getCounterExample formula [] = Nothing
getCounterExample formula (h@(World seq moreHypers):hypers) =
  let model = buildModelFromHypersequent h "0"
      world = makeWorldFromSequent seq "0"
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
addFormulaToModelAtWorld form mod old@(PossibleWorld true false tag) position =
  let newWorld = (case  position of
                     True  -> (PossibleWorld (form:true) false tag)
                     False -> (PossibleWorld true (form:false) tag))
      newModel = replaceWorldInModel mod old newWorld
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


buildModelFromHypersequent :: Hypersequent -> String -> Model
buildModelFromHypersequent hypersequent@(World seq hypers) rootTag =
  let (worlds, relations, _) =
        makeWorldsAndRelations hypersequent rootTag
   in Model worlds relations

makeWorldsAndRelations :: Hypersequent -> String -> ([PossibleWorld], [(PossibleWorld, PossibleWorld)], String)
--makeWorldsAndRelations  (World seq []) tag = 
--  let resultWorld = makeWorldFromSequent seq tag
--   in ([resultWorld],  [], (generateNextTag tag))
--makeWorldsAndRelations (World seq hypers) tag | trace ("FUNC " ++ show (World seq hypers) ++ " " ++ show tag) False = undefined
makeWorldsAndRelations (World seq hypers) tag = 
  let resultWorld = makeWorldFromSequent seq tag
   in foldl (\(accWorlds, accRelations, accTag) hyper@(World accSeq _) -> 
     let nextTag = generateNextTag accTag
         newRoot = makeWorldFromSequent accSeq nextTag
         (updatedWorlds, updatedRels, lastTag) = 
           makeWorldsAndRelations hyper nextTag
         newWorlds = accWorlds ++ updatedWorlds
         newRels = ((resultWorld, newRoot):accRelations) ++ updatedRels
      in (newWorlds, newRels, nextTag)) ([resultWorld], [], tag) hypers





--      (internalWorlds, internalRelations)  =
--        joinModelPairs . map (makeWorldsAndRelationsInternal newWorld) $ hypers
--   in ((newWorld:internalWorlds), ((newWorld,newWorld):internalRelations))

--makeWorldsAndRelationsInternal :: PossibleWorld -> Hypersequent -> ([PossibleWorld],  [(PossibleWorld, PossibleWorld)])
--makeWorldsAndRelationsInternal world (World seq hypers) =
--  let newWorld = makeWorldFromSequent seq
--      newRelations = [ (world, newWorld)
--                     , (newWorld, newWorld)]
--      (recursiveWorlds, recursiveRelations) =
--        joinModelPairs  . map (makeWorldsAndRelationsInternal newWorld) $ hypers
--      resultWorlds = [newWorld] ++  recursiveWorlds
--      resultRelations =
--        slowRemoveDuplicates $ newRelations ++ recursiveRelations
--   in  (resultWorlds, resultRelations)

joinModelPairs :: [([PossibleWorld], [(PossibleWorld, PossibleWorld)])] -> ([PossibleWorld], [(PossibleWorld, PossibleWorld)])
joinModelPairs [] = ([], [])
joinModelPairs ((worlds, relations):pairs) =
  let (recursiveWorlds, recursiveRelations) = joinModelPairs pairs
   in ((worlds ++ recursiveWorlds), (relations ++ recursiveRelations))


p = (AtomicFormula "p")
q = (AtomicFormula "q")
np = (Not p)
pandq = (And [p, q])
--f = (Necessarily
--     (Possibly
--      (Or [ (Necessarily p)
--          , (Necessarily (Possibly (And [ (Necessarily (Possibly (Not p)))
--                                        , (Possibly
--                                            (Necessarily
--                                              (Possibly (Not p))))])))])))
s1 = makeSequent  [] [p]
s5 = makeSequent [p] []

s2 = makeSequent [p] [q]
s3  = makeSequent [p] [np, pandq]
s4 = makeSequent [] [np]
h1  = (World (makeSequent [] []) [(World s1 []), (World  s5 [])])
h2 = (World s2 [(World s3 [(World s1 [])]), (World s4 [])])
f = (Implies (Implies (Implies  p q) p) p)
h = (World (makeSequent []  [])[(World (makeSequent []  [(Possibly (Not (AtomicFormula "p"))),(Possibly (And [(Possibly (Not (AtomicFormula "p"))),(Necessarily (Or [(Necessarily (AtomicFormula "q")),(Possibly (Not (AtomicFormula "p")))]))]))])[(World (makeSequent []  [(Possibly (Not (AtomicFormula "p"))),(Necessarily (AtomicFormula "q")),(Possibly (Not (AtomicFormula "p")))])[]),(World (makeSequent [(AtomicFormula "p"),(AtomicFormula "p")]  [(Possibly (Not (AtomicFormula "p"))),(Possibly (Not (AtomicFormula "p"))),(Possibly (Not (AtomicFormula "p")))])[(World (makeSequent [(AtomicFormula "p"),(AtomicFormula "p")]  [(Possibly (Not (AtomicFormula "p"))),(AtomicFormula "q")])[])]),(World (makeSequent []  [(Possibly (Not (AtomicFormula "p"))),(AtomicFormula "p")])[(World (makeSequent []  [(Possibly (Not (AtomicFormula "p"))),(Necessarily (AtomicFormula "q")),(Possibly (Not (AtomicFormula "p")))])[]),(World (makeSequent [(AtomicFormula "p"),(AtomicFormula "p")]  [(Possibly (Not (AtomicFormula "p"))),(Possibly (Not (AtomicFormula "p"))),(Possibly (Not (AtomicFormula "p")))])[(World (makeSequent [(AtomicFormula "p"),(AtomicFormula "p")]  [(Possibly (Not (AtomicFormula "p"))),(AtomicFormula "q")])[])])])])])
m = buildModelFromHypersequent h1 "0"
subs = disjuncts . negatum $ f
rs = getRelatedWorlds m (head (worlds m))
abcd = head rs
