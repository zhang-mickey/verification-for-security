{-# OPTIONS_GHC -Wno-orphans #-}

module Theory.Simplex
  ( simplex
  ) where

import CNF hiding (negate)
import Rename
import AST.LRA
import Theory.Class

import Control.Applicative (empty)
import Data.Ratio

import qualified Linear.Simplex.Types as Simplex
import qualified Linear.Simplex.Simplex as Simplex

deriving instance Ord Simplex.PolyConstraint

instance Theory Simplex.PolyConstraint where
  type Model Simplex.PolyConstraint = ()
  
--  solve :: Constraints a -> Maybe (Model a)
  solve constraints = do
    let deltaPos = Simplex.GEQ [(delta, 1)] (1 % 0xffffffff)
    let constraints' = deltaPos : fmap unlit constraints
    _ <- Simplex.findFeasibleSolution constraints'
    return ()

-- | The unique identifier used to write strict inequalities (>) and (<).
delta :: Integer
delta = 0xffffffff

-- | Transform a constraint into one without possible negation.
unlit :: Lit Simplex.PolyConstraint -> Simplex.PolyConstraint
unlit (Lit c) = c
unlit (Neg (Simplex.LEQ lhs rhs)) = Simplex.GEQ ((delta, 1):lhs) rhs
unlit (Neg (Simplex.GEQ lhs rhs)) = Simplex.LEQ ((delta, -1):lhs) rhs
unlit _ = error "Constraints should not contain equalities"

-- | Place the expression into its rigid linear form.
-- Such an expression is of the form:
-- a1 * x1 + a2 * x2 .. an * xn = b
--
-- You are *not* expected to transform the expression if it is not in this 
-- shape. Simply returning empty is sufficient in such a case!
--
-- You may want to look up the Simplex solver library to find out exactly
-- how it represents this linear form.
simplex :: LRA ID -> Maybe Simplex.PolyConstraint
-- simplex = undefined
simplex (lhs :<=: rhs) = do
  if constant(lhs)==Nothing
    then do 
  -- Convert the left-hand side and right-hand side expressions to linear forms
    linearLHS <- linear lhs
    linearRHS <- constant rhs
    return (Simplex.LEQ linearLHS linearRHS)
  else Nothing
    -- case (linearLHS, linearRHS) of
  --           ([(0, a)], (_)) -> Nothing
  --           _ -> return (Simplex.LEQ linearLHS linearRHS)
  -- Create a PolyConstraint for the <= relation

simplex (lhs :>=: rhs) = do
 if constant(lhs)==Nothing
    then do 
    linearLHS <- linear lhs
    linearRHS <- constant rhs
    return (Simplex.GEQ linearLHS linearRHS)
  else Nothing

-- | Place the expression into its rigid linear form.
-- Such an expression is of the form:
-- a1 * x1 + a2 * x2 .. an * xn
--
-- You are *not* expected to distribute the expression if it is not in this 
-- shape. Simply returning empty is sufficient in such a case!
-- type VarConstMap =[(Integer,Rational)]

linear :: Expr ID -> Maybe Simplex.VarConstMap
-- linear = undefined
linear (Var x) =  
  case variable (Var x) of 

    Just val  -> Just[(val, 1)]
    Nothing -> Nothing
    --Just [(variable x, 0)]
linear (Minus e) = do

  innerLinear <- linear e

  return [( a, negate x) | (a, x) <- innerLinear]

linear (lhs :+: rhs) = do
  linearLHS <- linear lhs
  linearRHS <- linear rhs
  return (linearLHS ++ linearRHS) 

--关键这两个函数怎么实现  
--    --怎么分配系数?
linear (Constant x) =  Just [(0,x)]
--8 * z + -4 * y + -x <= 14  乘法优先级最高
--除了constant*variable 其他_*_ return nothing  
    -- if  constant(lhs)==Nothing
linear(lhs:*:rhs:*:lst)=Nothing

-- linear(lhs:*:rhs:+:Minus lst)=Nothing
linear (lhs :*: rhs) = do
  case (variable lhs, variable rhs) of
    (Just val1, Just val2) -> Nothing
    _ -> do
      linearLHS <- linear lhs
      linearRHS <- linear rhs
      case (linearLHS, linearRHS) of
        ([(0, a)], [(v, b)]) -> Just [(v, a * b)]
        ([(v, a)], [(0, b)]) -> Just [(v, a * b)]
        _ -> Nothing
  --  if variable(lhs)/=Nothing $ variable(rhs)/=Nothing
  --   then do 
  --     linearLHS <- linear lhs
  --     linearRHS <- linear rhs 
  --     case (linearLHS, linearRHS) of
  --        ([(0, a)], [(v, b)]) -> Just [(v, a * b)]
  --        ([(v, a)], [(0, b)]) -> Just [(v, a * b)]
  --         _ -> Nothing

    
  --   else Nothing
-- | Convert the expression into just the Identifier if applicable.
--
-- Return 'empty' if the expression did not respresent a variable.
variable :: Expr ID -> Maybe Integer
--variable = undefined
variable (Var (ID x)) = Just x
-- variable(Minus x )= 
--   case variable x of 
--     Just val ->Just(negate val)
--     Nothing->Nothing
variable (Minus x) = fmap negate (variable x)
variable _ = Nothing

-- | Convert the expression to a Rational if applicable.
--
-- Return 'empty' if the expression did not respresent a constant.
constant :: Expr ID -> Maybe Rational
-- constant = undefined
constant (Constant r) = Just r 
-- constant(Minus r)=
--     case constant r of 
--     Just val ->Just(negate val)
--     Nothing->Nothing
constant (Minus r) = fmap negate (constant r)
constant _ = Nothing

