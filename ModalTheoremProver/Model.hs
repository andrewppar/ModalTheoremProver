module ModalTheoremProver.Model
  (Model (..)
  , satisfies
  , hypersequentSatisfies
  , getCounterExample
  , makeWorldsAndRelations
  , serializeModel
  )
    where
import ModalTheoremProver.Formula
import ModalTheoremProver.Sequent
import ModalTheoremProver.Hypersequent
import ModalTheoremProver.Utilities
import Data.Maybe
import qualified Data.Map as Map
import Debug.Trace
import Control.Parallel.Strategies
---------------
---- Models ---
---------------

data Model = Model {worlds :: [PossibleWorld]
                   , relations :: [(String, String)]
                   } deriving (Eq)

instance Show Model where
  show model =
    let ws = mapAppend (\w -> show w ++ "\n") . worlds $ model
        rs =
          mapAppend (\(r1,r2) -> r1 ++ " -> " ++ r2 ++ "\n") . relations $ model
     in "Worlds: \n " ++ ws ++ "\n" ++ "Relations: \n" ++ rs

serializeModel :: Serialization -> Model -> IO()
serializeModel HTML = serializeModelToHTML 

serializeModelToHTML :: Model -> IO()
serializeModelToHTML model = 
  do template <- readFile $ "./utilities/model_html_template.html"
     let templateLines  = lines template
         withWorlds     = addWorldsToTemplateLines templateLines model
         withRelations  = addRelationsToTemplateLines withWorlds model
         withKey        = addKeyToTemplateLines withRelations model
      in do writeFile "./utilities/Model.html" (unlines withKey)

addWorldsToTemplateLines :: [String]  -> Model -> [String]
addWorldsToTemplateLines [] _ = [] 
addWorldsToTemplateLines (line:lines) model = 
  if (filter (\x -> x /= ' ') line) == "NODES"
     then (generateWorldHTMLLines model) ++ lines
     else (line:(addWorldsToTemplateLines lines model))

generateWorldHTMLLines :: Model -> [String]
generateWorldHTMLLines model = 
  let modelWorlds = worlds model
      modelLines =  
        map (\world -> "{ id: " ++ (tag world) ++ ", reflexive: false} ") modelWorlds
   in (map (\line -> line ++ ",") (init modelLines)) ++ [(last modelLines)]

addRelationsToTemplateLines :: [String] -> Model -> [String] 
addRelationsToTemplateLines [] _ = [] 
addRelationsToTemplateLines (line:lines) model = 
  if (filter (\x -> x /=  ' ') line) == "RELATIONS"
     then (generateRelationsHTMLLines model) ++ lines
     else (line:(addRelationsToTemplateLines lines model))

generateRelationsHTMLLines  :: Model -> [String]
generateRelationsHTMLLines model = 
  let rels = relations model
      relationLines =
        map (\(relator, relatum) -> 
             "{ source: nodes[" ++ relator ++ "], target: nodes[" ++ relatum ++ "], left: false, right:  true}") rels
   in (map (\line -> line ++ ",") (init relationLines)) ++ [(last relationLines)]

addKeyToTemplateLines  ::  [String] -> Model -> [String]
addKeyToTemplateLines lines model = 
  let start = init lines
      header = "<h3>Key</h3>"
      modelWorlds = worlds model
      body = map (\world -> 
        let trues = joinStrings "," . map show . trueFormulas $  world
            falses  = joinStrings "," . map show . falseFormulas $ world
         in  "<p>World " ++ (tag world) ++ "<b>⊨</b>" ++ trues ++ "<b>⊭</b>" ++ falses ++ "</p>") modelWorlds
  in start ++ body ++ [(last lines)]

getWorldByTag :: Model -> String -> PossibleWorld
getWorldByTag model tagString = 
  --NOTE: This isn't safe 
 head . foldr 
           (\world acc -> 
             if tag world == tagString 
                then world:acc 
                else acc) [] . worlds $ model

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

formulaAtWorldP :: PossibleWorld -> Formula -> Bool 
formulaAtWorldP (PossibleWorld trues falses label) form = 
  form `elem` trues || form `elem` falses

getRelatedWorlds :: Model -> PossibleWorld -> [PossibleWorld]
getRelatedWorlds model@(Model worlds relations) =
  map (getWorldByTag model) 
 .  getRelatedWorldTags [] [] relations 
 . tag

getRelatedWorldTags :: [String]  -> [String] -> [(String, String)] -> String -> [String]
getRelatedWorldTags accumulator visitedTags relations tag = 
  let newVisitedTags = (tag:visitedTags) 
      oneStepRelated = 
        foldl (\acc (relator, relatum) -> 
          if relator == tag && relatum /= tag && not (relatum `elem` visitedTags)
             then (relatum:acc) 
             else acc) [] relations
      recursiveResults = 
        mapAppend (getRelatedWorldTags accumulator newVisitedTags relations) oneStepRelated
   in tag:recursiveResults

makeWorldFromSequent :: Sequent -> String -> PossibleWorld
makeWorldFromSequent (Sequent negs poss) tag =
  makeWorld (atoms negs) (atoms poss) tag
    where atoms = filter (\form -> atomicFormulaP form)

replaceWorldInModel :: Model -> PossibleWorld -> PossibleWorld -> Model
replaceWorldInModel (Model worlds relations) old new =
  let newWorlds = replaceWorldInWorlds worlds old new
   in (Model newWorlds relations)

replaceWorldInWorlds ::  [PossibleWorld] -> PossibleWorld -> PossibleWorld -> [PossibleWorld]
replaceWorldInWorlds [] _ _  = []
replaceWorldInWorlds (world:worlds) old new =
  if world == old
     then (new:(replaceWorldInWorlds worlds old new))
     else (world:(replaceWorldInWorlds worlds old new))

------------------
-- Satisfaction --
------------------

hypersequentSatisfies :: Formula -> Hypersequent -> Bool
hypersequentSatisfies formula hyper@(World seq hypers) =
  let models = buildModelsFromHypersequent  hyper "0"
      potentialSatisfiedModels = 
        map (\model -> satisfies formula model (getWorldByTag model "0")) models
      satisfiedModels = 
        potentialSatisfiedModels `using`parList rdeepseq
   in some (\x -> x == True) satisfiedModels

getCounterExample :: Formula -> [Hypersequent] -> Maybe Model
getCounterExample formula [] = Nothing
getCounterExample formula (h@(World seq moreHypers):hypers) =
  let models = buildModelsFromHypersequent h "0"
      world = makeWorldFromSequent seq "0"
      survivingModels = 
        filter (\model -> 
          let (newModel, maybeVal) =
                satisfiesInternal (Not formula) model  world
           in case maybeVal of  
             Just True -> True
             otherwise -> False) models
 in if survivingModels == [] 
       then Nothing
    else Just (head survivingModels)

satisfies :: Formula -> Model -> PossibleWorld -> Bool
satisfies form model world =
  if world `elem` (worlds model)
     then let (updatedModel, value) = satisfiesInternal form model world
           in case value of
             Just value -> value
             Nothing -> False
     else False

debugMode = False
satisfiesIntermediate  :: Formula -> Model -> PossibleWorld -> (Model, Maybe Bool)
satisfiesIntermediate formula model  world = 
  if debugMode 
     then trace ("SatisfiesInternal: " ++ (show formula) ++ " " ++ (tag world)) (satisfiesInternal formula model world)
     else satisfiesInternal formula model world

satisfiesInternal :: Formula -> Model -> PossibleWorld -> (Model, Maybe Bool)
-- TODO: There are probably  some good  abstractions  to  be made
-- in the quantified parts of this
satisfiesInternal form@(AtomicFormula string) model world = 
  if form `elem` (trueFormulas world)
     then (model, Just True)
     else if form `elem` (falseFormulas world)
             then (model, Just False)
             else (model, Nothing)
satisfiesInternal (Not (AtomicFormula string)) model world =
 if (AtomicFormula  string) `elem` (trueFormulas world)
    then (model, Just False)
    else if (AtomicFormula string)  `elem` (falseFormulas world)
         then (model, Just True)
         else (model, Nothing)
satisfiesInternal (Not form) model world =
  let (newModel, recursiveValue) = satisfiesIntermediate form model world
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

satisfiesJunctionInternal :: [Formula] -> Model -> PossibleWorld -> Bool -> (Model, Maybe Bool)
satisfiesJunctionInternal [] model _ startingValue =
  (model, Just startingValue)
satisfiesJunctionInternal (x:xs) model world startingValue =
  let (m, maybeValue) = satisfiesInternal x model world
   in  case maybeValue of 
     Just value -> 
       if value /= startingValue 
          then (m, maybeValue)
          else satisfiesJunctionInternal  xs model world startingValue
     otherwise -> satisfiesJunctionInternal xs model world startingValue

satisfiesModalInternal :: Formula -> Model -> [PossibleWorld] -> Bool -> (Model, Maybe Bool)
satisfiesModalInternal _ model [] startingValue =
  (model, Just startingValue)
satisfiesModalInternal form model (world:worlds) startingValue =
  let (m, maybeValue) = satisfiesIntermediate form model world
   in case maybeValue of
     Just value ->
       if value /= startingValue
          then (m, Just value)
          else satisfiesModalInternal form m worlds startingValue
     otherwise -> satisfiesModalInternal form m worlds startingValue

buildModelsFromHypersequent :: Hypersequent -> String -> [Model]
buildModelsFromHypersequent hypersequent@(World seq hypers) rootTag =
  let (worlds, relations, _) = makeWorldsAndRelations hypersequent rootTag
      baseModel = (Model worlds relations)
      atoms = gatherAtomicFormulasInHypersequent hypersequent
   in completeModelWithFormulas baseModel atoms

makeWorldsAndRelations :: Hypersequent -> String -> ([PossibleWorld], [(String, String)], String)
makeWorldsAndRelations (World seq hypers) rootTag =
  let resultWorld = makeWorldFromSequent seq rootTag
   in foldl (\(accWorlds, accRelations, accTag) hyper@(World accSeq _) ->
     let nextTag = generateNextTag accTag
         newRoot = makeWorldFromSequent accSeq nextTag
         (updatedWorlds, updatedRels, lastTag) =
           makeWorldsAndRelations hyper nextTag
         newWorlds = accWorlds ++ updatedWorlds
         resultTag = (tag resultWorld)
         newRootTag = tag newRoot
         newRels = ((resultTag, newRootTag):accRelations) ++ updatedRels
      in (newWorlds, newRels, lastTag)) ([resultWorld], [], rootTag) hypers

completeModelWithFormulas :: Model -> [Formula] -> [Model]
completeModelWithFormulas model forms = 
  foldl (\acc form -> 
    if  acc == [] 
       then completeModelWithFormula model form 
       else mapAppend (\model -> 
         completeModelWithFormula model form) acc) [] forms

completeModelWithFormula :: Model -> Formula -> [Model]
completeModelWithFormula base@(Model [] _) _ =  [base]
completeModelWithFormula base@(Model (world:worlds) relations) form = 
  let recursiveModels = completeModelWithFormula (Model worlds relations) form
   in if formulaAtWorldP world form
         then map (\(Model ws rs) -> (Model (world:ws) rs)) recursiveModels
         else foldl (\acc (Model ws rs) -> 
           let newTrueWorld = addTrueFormula world form
               newTrueModel = (Model (newTrueWorld:ws) relations)
               newFalseWorld = addFalseFormula world form
               newFalseModel = (Model (newFalseWorld:ws) relations)
            in (newTrueModel:newFalseModel:acc)) [] recursiveModels

p = (AtomicFormula "p")
q = (AtomicFormula "q")

s0 = makeSequent [p,q]  []
s1 = makeSequent [p] []
s2 = makeSequent []  [p,q]

h1 = (World s0 [(World s2 [])])
m1 = buildModelsFromHypersequent h1 "0"

f = (Necessarily (Possibly (Or [(Necessarily p), (And [p, (Not p)])]))) 
h = (World (makeSequent []  [])[(World (makeSequent []  [(Possibly (Or [(Necessarily (AtomicFormula "p")),(And [(AtomicFormula "p"),(Not (AtomicFormula "p"))])])),(Or [(Necessarily (AtomicFormula "p")),(And [(AtomicFormula "p"),(Not (AtomicFormula "p"))])])])[])]) 
  
m = buildModelsFromHypersequent h "0"
