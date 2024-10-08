module CNF.DPLL
  ( Solution
  , resolve
  , ple
  , bcp
  , branch
  , dpll
  , satisfiable
  ) where

import Prelude hiding (negate)

import CNF.Types

import Data.Functor.Identity (runIdentity)
import Data.Maybe (mapMaybe)
--
import Data.List
import Control.Applicative
--filterM
import Control.Monad ((>=>), foldM,filterM)
import Control.Monad.Writer
import Control.Monad.Trans.Maybe (runMaybeT)
import CNF.Transform (cnf)

-- | A solution given by the DPLL algorithm.
type Solution a = [Lit a]

-- | A monad m solves over the type a with the following constraints.
type Solver a m = (MonadWriter (Solution a) m, Alternative m, Eq a)




-- | Unit Resolution
--
-- Given a literal and a CNF, remove all occurences of it in the CNF according
-- to Unit Resolution. This implementation can be useful in all three stages
-- of the DPLL algorithm.
--
-- e.g. resolve (Lit p) [[Lit p], [Lit q], [Neg p]] == [[Lit q], []]
--
-- Notice how an occurence of the literal resolves the whole Or while occurence
-- of its negation removes the literal. You may assume that any literal occurs
-- in any given Or at most once.
--
-- Make sure to add the literal that will be resolved to the solution via
-- a call to 'tell'!
resolve :: Solver a m => CNF a -> Lit a -> m (CNF a)
-- resolve = undefined
-- resolve cnf lit= do
--   tell[lit]
--   return  $ filter (notElem lit ) cnf
resolve cnf lit = do
  let notElemcnf = [clause | clause <- cnf,  lit `notElem` clause]
  let resolved = [filter (\l -> l /= negate lit) clause | clause <- notElemcnf]
  tell [lit]
  return resolved


-- | Pure Literal Elimination (PLE)
--
-- Resolve variables if they only occur positively or
-- negatively (but not both), according to Pure Literal
-- Elimination
--
-- Do make sure to remove new pure literals that
-- occur due to PLE!
--ple :: Solver a m => CNF a -> m (CNF a)
--ple = undefined
  -- let lit =head cnf
  -- let q =tail cnf
  -- let pureliterals = [clause |clause <- cnf, negate clause `notElem` cnf]
ple :: Solver a m => CNF a -> m (CNF a)
ple cnf = do
  pureLiterals <- findPureLiterals cnf
  case pureLiterals of 
    [] -> return cnf
    _ -> do
      x <- foldM resolve cnf pureLiterals
      ple x

findPureLiterals :: Solver a m => CNF a -> m [Lit a]
findPureLiterals cnf = do
  let literals = concat cnf
      isPure lit = negate lit `notElem` literals
      pureLiterals = [lit | lit <- literals, isPure lit]  
  return pureLiterals


-- | Boolean Constraint Propagation (BCP)
--
-- Remove all occurences of single variables according
-- to Boolean Constraint Propagation.
--
-- Do make sure to remove new single occurences that
-- occur due to BCP!
bcp :: Solver a m => CNF a -> m (CNF a)
--bcp = undefined
bcp cnf = do
  let unitClauses = [clause | clause <- cnf, length clause == 1] 
  case unitClauses of
    [] -> return cnf -- No unit clauses left, BCP complete
    _ -> do
      let unitLiterals = nub [lit | [lit] <- unitClauses]
      tell unitLiterals
      --foldM resolve cnf unitLiterals>>=bcp
      newCNF <- foldM resolve cnf unitLiterals
      bcp newCNF

-- | Attempts to solve the constraints by resolving
-- the given literal. Picking a constraint in this
-- way may fail the recursive dpll call, which is
-- why this function is call 'try'.
--
-- You may want to implement this function as a
-- helper for 'branch'.
try :: Solver a m => CNF a -> Lit a -> m ()
try cnf lit = do
  resolvedCnf <- resolve cnf lit
  case resolvedCnf of
    [] -> return ()
    _  -> branch resolvedCnf -- Continue with the resolved CNF

-- | Branch in the Depth First Search. (i.e. try both occurences of a variable)
--
-- Three cases may happen here:
-- - There is no more solution for this branch (i.e. empty disjunct [] exists).
--   Signify failure via 'empty'
--
-- - There is a variable to choose. 
--   'try' both a positive and negative occurence.
--   Hint: Use (<|>) 
--
-- - There is *no* more variable to choose.
--   This branchs offers a solution! Signify succes via 'return ()'
--
-- Return type: You may return `pure ()` when it is satifiable and `empty`
-- otherwise. This will also allow you to compose branches via the (<|>)
-- operator. More precisely, for two functions f1 and f2, f1 <|> f2 will first
-- try if f1 succeeds (in our case, succeeding means proving satisfiability),
-- and if not, try f2. This will be useful when assigning tentative values to
-- Boolean variables.
--
-- We don't expect any heuristics to pick branches in this implementation. Thus,
-- you may just pick any literal to branch on.


branch :: Solver a m => CNF a -> m ()
branch cnf = do
  case cnf of
    [] -> return () -- This branch offers a solution, signify success
    [[]] -> return empty()
    (clause:_) -> do
      case clause of
        [] -> return empty()
        (lit:_) -> do
          try cnf lit <|> try cnf (negate lit)

-- | The DPLL procedure. 
--
-- Finds whether a given CNF is satisfiable.
--
-- A CNF is satisfiable when all of its conjuncts are resolved. In our case,
-- when we have [] :: CNF a
--
-- A CNF is unsatisfiable when it contains an Or that contains no literals.
-- e.g., [[], ...] is unsat
dpll :: Solver a m => CNF a -> m ()
dpll = ple >=> bcp >=> branch

-- | Check a given CNF for satisfiability. Returning a model
-- when there is one.
satisfiable :: Eq a => CNF a -> Maybe (Solution a)
satisfiable = runIdentity . runMaybeT . execWriterT . dpll
