module CNF.Transform
  ( distribute
  , cnf
  ) where

import AST.Prop
--
import Data.List
import CNF.Types (CNF)
import qualified CNF.Types as CNF

-- | This function implements the distribution 
-- of disjunction over conjunction.
--
-- The function takes as arguments two 
-- propositions p and q, representing formula p | q, 
-- and exhaustively applies the distribution operation.
--
-- An example of a distribution:
--
-- $ distribute (a & b & c) (d & (e | f))
-- > (a | d) & (a | e | f) & (b | d) & (b | e | f) & (c | d) & (c | e | f)
--
-- Note that this solution will be in the rigid CNF format, which
-- means that the actual result will look more like:
--
-- $ distribute [a, b, c] [d, [e, f]]
-- > [ [a, d], [a | e | f], [b, d], [b, e, f], [c, d], [c, e, f] ]
--
-- Note: While it is technically correct to order the distribution differently
-- (modulo commutativity), this is a nightmare to check programatticaly. For
-- this reason, we require your implementation to distribute in the order shown
-- above!
--
-- Hint: You may want to define a helper function that distributes a single Or
-- over the entire second argument.
--
-- Though won't grade on it, you can try to implement this function without
-- pattern matching on the lists. Haskell already provides a lot of functions
-- to operate on lists!
-- distribute :: CNF a -> CNF a -> CNF a


distributeOrOverCNF :: CNF a -> [CNF.Lit a] -> CNF a
distributeOrOverCNF q orClause = [ lit : disj | disj <- q , lit <- orClause ]

distribute :: CNF a -> CNF a -> CNF a
distribute [] q = [] 
distribute [p][q] = [p++q]
distribute (p:ps) q =
  let distributedOr = distributeOrOverCNF q p
  in distributedOr ++ distribute ps q  -- Recursively distribute the rest of p over q.

-- distribute [] q = q
-- distribute (p:ps) q = singleor p (distribute ps q)
-- distribute ps q 
--   | length (head ps)==1=foldr singleor ps q
--   | otherwise =foldr singleor q ps

-- distribute ps q = foldr singleor q ps
-- singleor::CNF.Or a-> CNF a-> CNF a
-- singleor _ [] = []
-- singleor [] _ = []
-- singleor p (q:qs)=(p++q):singleor p qs

-- singleor p@(x:xs) q@(y:ys)
--   | length p == 1 = (x : y) : singleor xs q
--   | otherwise      = (y ++ p) : singleor xs q
-- if length p ==1
--   then singleor (p:ps) (q:qs) = (p++q):singleor p qs
--   else singleor (p:ps) (q:qs) = (q++p):singheor q ps

-- singleor p (q:qs)=(p++q):singleor p qs
-- singleor p qs = map (p ++) qs
-- singleor p = map (p ++)


-- | Converts a proposition into a rigid CNF.
--
-- Cases of interest your code has to handle for a correct CNF implemention:
-- - Literals and their Negation
-- - Connectives
-- - Double negative
-- - Negatives over connectives
--
-- Note that as the names Neg and Lit are both defined in Prop and CNF, you
-- need to use CNF.Lit or CNF.Neg to differentiate them from those defined in
-- Prop.
--
-- Hint: [[CNF.Neg p]] = !p
--
-- Why do we have a separate type for CNF instead of Prop?
-- - CNF is a rigid form of Prop; it can only ever represent formulas in CNF.
--   Prop may represent formulas in CNF, but also  other formulas. Using the
--   rigid form allows us to avoid runtime checks to see whether a Prop is in
--   CNF as needed for DPLL.
-- cnf :: Prop a -> CNF a
-- --cnf = undefined


cnf :: Prop a -> CNF a
cnf (Lit x) = [[CNF.Lit x]]
cnf (Neg (Lit x)) = [[CNF.Neg x]]
cnf (Neg (Neg p)) = cnf p
cnf (p :&: q) = cnf p ++ cnf q  -- Conjunction
cnf (p :|: q) = [clause1 ++ clause2 | clause1 <- cnf p, clause2 <- cnf q]  -- Disjunction
cnf (Neg (p :&: q)) = [clause1 ++ clause2 | clause1 <- cnf (Neg p), clause2 <- cnf (Neg q)]  -- De Morgan's Law for Neg (p :&: q)
cnf (Neg (p :|: q)) = cnf (Neg p) ++ cnf (Neg q)  -- De Morgan's Law for Neg (p :|: q)
