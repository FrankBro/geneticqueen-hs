--module GeneticQueen where

import Control.Applicative ((<$>))
import Control.Monad.State
import Data.List
import Data.Maybe
import Debug.Trace
import System.Random

type Position   = Int
type Individual = [Position]
type Population = [Individual]
type Couple     = (Individual, Individual)
type Couples    = [Couple]

type RandomState a = State StdGen a

main :: IO ()
main = do
  gen <- newStdGen
  let nbQueen = 8
  let popSize = 20
  let birthRate = 0.5
  let mutationRate = 0.5
  let iterations = 100
  let (pop, gen') = runState (createPopulation nbQueen popSize) gen
  mapM_ print $ printPopulation pop
  print "---"
  let solution = evalState (run pop nbQueen popSize birthRate mutationRate iterations) gen'
  mapM_ print $ printPopulation solution
-----------------------------------
-- * Print
-----------------------------------
printPopulation :: Population -> [String]
printPopulation p =
  (printIndividual <$> p ) ++ [show (average p)]

printIndividual :: Individual -> String
printIndividual i =
  show i ++ " -> " ++ show (calcConflicts i)

average :: Population -> Int
average p = (sum $ calcConflicts <$> p) `div` (length p)
-----------------------------------
-- * Algo
-----------------------------------

-- Run the algorithm for the number of iteration provided
run :: Population -> Int -> Int -> Double -> Double -> Int -> RandomState Population
run pop nbQueen popSize birthRate mutationRate iter
  | iter == 0 = return pop
  | otherwise = do
    gen <- get
    let (pop', gen') = runState (generation pop nbQueen popSize birthRate mutationRate) gen
    put gen'
    return $ evalState (run pop' nbQueen popSize birthRate mutationRate (iter - 1)) gen'

-- Handles a single generation, creating a new population
generation :: Population -> Int -> Int -> Double -> Double -> RandomState Population
generation parents nbQueen popSize birthRate mutationRate = do
  gen <- get
  let (children, gen') = runState (reproduction parents birthRate nbQueen) gen
  let (mutants, g)  = runState (mutation children mutationRate nbQueen) gen'
  let (parents', g') = runState (selection (parents ++ children ++ mutants) popSize) g
  put g'
  return parents'

-- Creates children from the parent population using the birth rate
reproduction :: Population -> Double -> Int -> RandomState Population
reproduction parents birthRate nbQueen = do
  gen <- get
  let indexedParents = zip parents [1..]
  let couples = [ (a, b) | a <- indexedParents, b <- indexedParents]
  let childrenFun = sequence $ map (\x -> reproduce x birthRate nbQueen) couples
  let (children, gen') = runState childrenFun gen
  put gen'
  return $ catMaybes children

-- Creates couples based on 2 factors :
--   (1) The 2 parents are not the same
--   (2) A chance based on the birth rate
reproduce :: ((Individual, Int),(Individual, Int)) -> Double -> Int -> RandomState (Maybe Individual)
reproduce ((a, ia), (b, ib)) birthRate nbQueen
  | ia == ib = return Nothing
  | otherwise = do
    gen <- get
    let (p, gen') = runState (getBoundedRandom (0.0, 1.0 :: Double)) gen
    if p <= birthRate then do
      put gen'
      return Nothing
    else do
      let (child, g) = runState (produceChild a b nbQueen) gen'
      put g
      return (Just child)

-- Produce a child from the 2 parents
produceChild :: Individual -> Individual -> Int -> RandomState Individual
produceChild a b nbQueen = do
  gen <- get
  let (s, gen') = runState (getBoundedRandom (0, nbQueen - 1)) gen
  let (p, g) = runState (getBoolRandom) gen'
  put g
  if p == True then do
    return $ (fst $ splitAt' s a) ++ (snd $ splitAt' s b)
  else do
    return $ (fst $ splitAt' s b) ++ (snd $ splitAt' s a)

-- Creates mutants from the children using the mutation rate
mutation :: Population -> Double -> Int -> RandomState Population
mutation children mutationRate nbQueen = do
  gen <- get
  let mutantFun = sequence $ map (\x -> mutate x mutationRate nbQueen) children
  let (mutants, gen') = runState mutantFun gen
  put gen'
  return $ catMaybes mutants

-- Create a mutant based on the mutation rate
mutate :: Individual -> Double -> Int -> RandomState (Maybe Individual)
mutate c mutationRate nbQueen = do
  gen <- get
  let (p, gen') = runState (getBoundedRandom (0.0, 1.0 :: Double)) gen
  if p <= mutationRate then do
    put gen'
    return Nothing
  else do
    let (mutant, g) = runState (produceMutant c nbQueen) gen'
    put g
    return (Just mutant)

-- Produce a mutant from a child
produceMutant :: Individual -> Int -> RandomState Individual
produceMutant c nbQueen = do
  gen <- get
  let ((a,b), gen') = runState (getTwoDiffBoundedRandom (0, nbQueen - 1)) gen
  put gen'
  return $ swap a b c

-- Apply selection on the population, reducing it to the population size
-- Will call itself until it fits
selection :: Population -> Int -> RandomState Population
selection population popSize = do
  let uniquePopulation = rmdups population
  gen <- get
  let (pop, gen') = runState (reducePop uniquePopulation popSize) gen
  put gen'
  return pop

-- This function is temporary, need to keep RandomState
reducePop :: Population -> Int -> RandomState Population
reducePop population popSize
  | length (population) <= popSize = return population
  | otherwise = do
    gen <- get
    let (pop, gen') = runState (killOne' population ) gen
    put gen'
    return $ evalState (reducePop pop popSize) gen'

-- This function is temporary, need to keep RandomState
-- TODO, pick a random instead of the first if conflict is equal
killOne' :: Population -> RandomState Population
killOne' pop = do
  gen <- get
  let ((a,b), gen') = runState (getTwoDiffBoundedRandom (0, (length pop) - 1)) gen
  let iA = pop !! a
  let iB = pop !! b
  let pop' = delete iA $ delete iB pop
  -- TODO, pick a random instead of the first if conflict is equal
  put gen'
  if calcConflicts iA <= calcConflicts iB then return $ iA : pop'
                                          else return $ iB : pop'

-- Return the number of conflicts for an indidual
calcConflicts :: Individual -> Int
calcConflicts i =
  foldl (\acc x -> acc + (calcConflicts' x indexedIndividual)) 0 indexedIndividual
  where indexedIndividual = zip i [0..]

calcConflicts' :: (Int, Int) -> [(Int, Int)] -> Int
calcConflicts' x xs =
  rC + uC + dC
  where conflict f = foldl (\acc y -> if snd x <= snd y then acc else f y xs) 0 xs
        rC = conflict rightConflict'
        uC = conflict upConflict'
        dC = conflict downConflict'

rightConflict' :: (Int, Int) -> [(Int, Int)] -> Int
rightConflict' x xs =
  foldl' foldFun 0 xs
  where isValid x y = (isG x y) && (fst x == fst y)
        foldFun acc y = if isValid x y then acc + 1 else acc

upConflict' :: (Int, Int) -> [(Int, Int)] -> Int
upConflict' x xs =
  foldl' foldFun 0 xs
  where isValid x y = (isG x y) && (fst x == adjust y)
        foldFun acc y = if isValid x y then acc + 1 else acc
        adjust y = fst y - (snd y - snd x)

downConflict' :: (Int, Int) -> [(Int, Int)] -> Int
downConflict' x xs =
  foldl' foldFun 0 xs
  where isValid x y = (isG x y) && (fst x == adjust y)
        foldFun acc y = if isValid x y then acc + 1 else acc
        adjust y = fst y + (snd y - snd x)

isG :: (Int, Int) -> (Int, Int) -> Bool
isG x y = snd y > snd x
----------------------------------
-- * Init
----------------------------------

-- Create a population of (Population size) individuals, each one containing (Number of queen).
createPopulation :: Int -> Int -> RandomState Population
createPopulation nbQueen popSize = mapM (\x -> createIndividual nbQueen) [1..popSize]

-- Create an individual, contraining (Number of queen).
createIndividual :: Int -> RandomState Individual
createIndividual nbQueen = mapM (\x -> runBoundedRandom (0, nbQueen - 1)) [1..nbQueen]
----------------------------------
-- * Util
----------------------------------
getBoundedRandom :: Random a => (a,a) -> RandomState a
getBoundedRandom bnds = do
  gen <- get
  let (val, gen') = randomR bnds gen
  put gen'
  return val

runBoundedRandom :: Random a => (a,a) -> RandomState a
runBoundedRandom bnds = do
  oldState <- get
  let (result, newState) = runState (getBoundedRandom bnds) oldState
  put newState
  return result

getBoolRandom :: RandomState Bool
getBoolRandom = do
  gen <- get
  let (val, gen') = random gen
  put gen'
  return val

runBoolRandom :: RandomState Bool
runBoolRandom = do
  oldState <- get
  let (result, newState) = runState (getBoolRandom) oldState
  put newState
  return result

getTwoDiffBoundedRandom :: (Random a, Eq a) => (a,a) -> RandomState (a,a)
getTwoDiffBoundedRandom bnds = do
  gen <- get
  let (a, gen') = runState (getBoundedRandom bnds) gen
  let (b, g   ) = runState (getBoundedRandom bnds) gen'
  put g
  if a == b then do
    return $ evalState (getTwoDiffBoundedRandom bnds) g
  else do
   return (a,b)

splitAt' :: Int -> [a] -> ([a], [a])
splitAt' 0 xs     = ([], xs)
splitAt' _ []     = ([], [])
splitAt' n (x:xs) = (x:xs', xs'')
  where
    (xs', xs'') = splitAt (n - 1) xs

swap :: Int -> Int -> [a] -> [a]
swap i j xs | i == j    = xs
swap i j xs | otherwise = initial ++ (xs !! b) : middle ++ (xs !! a) : end
    where [a,b] = sort [i,j]
          initial = take a xs
          middle  = take (b-a-1) (drop (a+1) xs)
          end     = drop (b+1) xs

rmdups :: (Ord a) => [a] -> [a]
rmdups = map head . group . sort
