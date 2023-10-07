module SMT
  ( smt
  ) where

import Prelude hiding (negate)

import Rename ( lookupName, ID, Renames )
import CNF
import AST.Prop (Prop)
import Theory.Class 
import Theory.Simplex
import Control.Applicative
import Data.Maybe (mapMaybe)
--W
-- import Data.Set (Set)
-- import qualified Data.Set as Set

-- | Rename a solution so it becomes a set of constraints for a Theory.
--
-- Notice that Solution and Constraints are essentially the same type
-- under a different name.

---- | A solution given by the DPLL algorithm.
--    type Solution a = [Lit a]
asConstraints :: Renames a -> Solution ID -> Constraints a
asConstraints renames solution =
  let constraintList = mapMaybe (\case
                                    Lit ident -> fmap Lit (lookupName renames ident)
                                    Neg ident -> fmap Neg (lookupName renames ident)
                                  
                                ) solution
  in constraintList


dpllT :: Theory a => CNF ID -> Renames a -> Maybe (Model a)
dpllT cnfID renames =
  let model = satisfiable cnfID
      constraints = case model of
                     Just m -> m
                     Nothing -> []
  in if areContradictoryConstraints constraints
     then Nothing
     else do
       let theoryConstraints = asConstraints renames constraints
       case solve theoryConstraints of
         Just theoryModel -> return theoryModel
         Nothing -> do
           case model of
             Just m -> do
                let negatedCNF = addNegation cnfID m
                dpllT negatedCNF renames
             Nothing -> Nothing

  where
    addNegation :: CNF ID -> Solution ID -> CNF ID
    addNegation cnf [] = cnf
    addNegation cnf (x:xs) = addNegation (addNegatedLiteral cnf x) xs

    addNegatedLiteral :: CNF ID -> Lit ID -> CNF ID
    addNegatedLiteral cnf (Lit ident) = cnf ++ [[Neg ident]]
    addNegatedLiteral cnf (Neg ident) = cnf ++ [[Lit ident]]

    areContradictoryConstraints :: Constraints ID -> Bool
    areContradictoryConstraints [] = False
    areContradictoryConstraints (Lit ident : xs) = Neg ident `elem` xs || areContradictoryConstraints xs
    areContradictoryConstraints (Neg ident : xs) = Lit ident `elem` xs || areContradictoryConstraints xs





-- asConstraints :: Renames a -> Solution ID -> Constraints a
-- --asConstraints = undefined
-- asConstraints renames solution =
--   let constraintList = mapMaybe (\case
--                                     Lit ident -> fmap Lit (lookupName renames ident)
--                                     Neg ident -> fmap Neg(lookupName renames ident)
                                  
--                                 ) solution
--   in constraintList
  --mapMaybe (\ident -> lookupName renameMap ident) solution
  


-- | The DPLL(T) algorithm.
--
-- Extends the normal DPLL algorithm to work over theorems.
-- This implementation solves only over a single theorem at a time.
--
-- The algorithm works as follows:

--
-- Notice how in step 3b we essentially tell the SAT solver to not pick this
-- specific solution via the additional constraints. Otherwise the SAT solver 
-- would infinitely pick the same solution! 
--
-- Hint: Check the 'Theory' typeclass.
  --输入是(x+y=1 | z+w=2) & !(x+y=2 & z+w=1) LRA 非CNF form
  --LRA怎么到（p|q）&!(p&q)?
  --之后tseitin转成 CNF form
  --通过dpll找model
  --找不到 Nothing
  --找到的话将dpll返回的model变成LRA形式 
    --怎么solve LRA?  solve
  --solve LRA 成功的话返回model
  --不成功 dpllT（(p|q）&!(p&q) & negate model）
-- dpllT :: Theory a => CNF ID -> Renames a -> Maybe (Model a)
-- dpllT cnfID renames = do
--   -- 1. Find a solution over a CNF ID, negligent of what the IDs represent.
--   case satisfiable cnfID of
--     -- a. On success, return the model
--     Nothing -> Nothing
--     Just model -> do
--       -- 2. Convert Renames a to constraints
--       let theoryConstraints = asConstraints renames model

--       -- 3. Try to solve the theory constraints.
--       case solve theoryConstraints of
--         Just theoryModel -> return theoryModel
--         -- b. On failure, strengthen the CNF with negation and recurse
--         Nothing -> do
--           let litToNegate = negateLiteral model
--           let newCNF=cnfID++[[litToNegate]]
--           dpllT newCNF renames
--     -- c. On failure to find a solution, return Nothing

-- negateLiteral :: Solution ID -> Lit ID
-- negateLiteral [] = error "Cannot negate an empty model"
-- negateLiteral (x:_) = negate x

-- dpllT :: Theory a => CNF ID -> Renames a -> Maybe (Model a)
-- dpllT cnfID renames = do
--   -- 1. Find a solution over a CNF ID, negligent of what the IDs represent.
--   -- 2. Convert Renames a to constraints
--   let model = satisfiable cnfID
--       constraints = case model of
--                      Just m -> m
--                      Nothing -> []
--   let theoryConstraints = asConstraints renames constraints

--   -- 3. Try to solve the theory constraints.
--   case solve theoryConstraints of
--     -- a. On success, return the model
--     Just theoryModel -> return theoryModel
--     -- b. On failure, strengthen the CNF with negation and recurse
--     Nothing -> do
--       case model of
--         Just m -> do
--            let litToNegate = negateLiteral m
--            dpllT (cnfID ++ [[litToNegate]]) renames
--         Nothing -> Nothing 

-- negateLiteral :: Solution ID -> Lit ID
-- negateLiteral [] = error "Cannot negate an empty model"
-- negateLiteral (x:_) = negate x



-- | Run the SMT solver on a proposition over some solvable
-- theory.
smt :: (Theory a, Ord a) => Prop a -> Maybe (Model a)
smt = uncurry dpllT . equisat        
