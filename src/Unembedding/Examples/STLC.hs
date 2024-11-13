{-

An unembedded implementation of the Simply Typed Lambda Calc

The lambda calc does not need to be unembedded, but is a simple way to show how
to unembed a language.

-}

{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Unembedding.Examples.STLC where

-- base
import           Control.Monad         (join)
import           Data.Foldable         (toList)
import           Data.Functor.Identity (Identity (..))

-- containers
import           Data.Sequence         (Seq)
import qualified Data.Sequence         as S

-- unembedding tooling
import qualified Unembedding           as UE
import           Unembedding           (Dim (..), EnvI (..), LiftVariables,
                                        TEnv, Variables (..), ol0, ol1, runOpen)
import           Unembedding.Env

-- Unembedding recipe:
-- -------------------
-- 1. Identity semantic domain
-- 2. Prepare semantic functions for each construct
-- 3. Provide HOAS rep of syntax
-- 4. Implement HOAS functions by lifting semantic functions
-- Now you can interpret open expressions if you want (dont say if you want in paper)

-- overall: usage-wise, the recipe is easy to understand and replicate, and the
-- under the hood is fiddly, but routine

-- Step 1: Identity semantic domain
-- -----------------------------------------------------------------------------
-- This will be an instance of the Variables type class


-- | The semantic domain of the STLC is just normal functions, taking an enviroment
--   of free variable assignments to a result.
newtype STLC env a = Sim { runSim :: VEnv env -> a }
type VEnv = Env Identity

-- the featuring of an env in this function makes making a variables instance easy

instance Variables STLC where
  var :: STLC (a ': as) a
  var = Sim (\(ECons (Identity x) _) -> x)
  weaken :: STLC as a -> STLC (b ': as) a
  weaken (Sim f) = Sim (\(ECons _ env) -> f env)

instance LiftVariables STLC STLC where
  liftVar = id

-- Step 2: Prepare semantic functions for each construct
-- -----------------------------------------------------------------------------
-- The constructs that we will support are:
--  * lam
--  * app

lamSem :: STLC (a ': env) b -> STLC env (a -> b)
lamSem bTerm = Sim (\e x ->
  let e' = ECons (Identity x) e -- Add x :: a to env.
  in runSim bTerm e')           -- Use to make b.

appSem :: STLC env (a -> b) -> STLC env a -> STLC env b
appSem fTerm aTerm = Sim (\e ->
  let f = runSim fTerm e -- Unpack function using e.
      x = runSim aTerm e -- Unpack arg using e.
  in f x) -- Apply.

-- Step 3: Provide HOAS rep of syntax
-- -----------------------------------------------------------------------------

-- | Classic HOAS STLC, letting haskell handle the variables
class STLChoas exp where
  lam :: (exp a -> exp b) -> exp (a -> b)
  app :: exp (a -> b) -> exp a -> exp b

-- Step 4: Implement HOAS functions by lifting semantic functions
-- -----------------------------------------------------------------------------

instance STLChoas (EnvI STLC) where
  app = UE.liftFO2 appSem -- not a binder => FO, 2 args => FO2
  lam = UE.liftSOn (ol1 :. End) lamSem -- binder => SO

-- Now you can interpret open expressions if you want
-- -----------------------------------------------------------------------------

-- | Wrapper function around runOpen that ensures that our STLC term does indeed
--  only have one arg
runOpenSTLC :: (forall exp . STLChoas exp => exp a -> exp b) -> STLC '[a] b
runOpenSTLC f = runOpen f

-- | Runs a STLC expression with one free var, where the user provides the value
--   of a free var as an arg
runSTLC :: STLC '[a] b -> a -> b
runSTLC t x = let e = ECons (Identity x) ENil in runSim t e

-- example:

exSTLC :: STLC '[Int] Int
exSTLC = runOpenSTLC term

term :: STLChoas exp => exp b -> exp b
term x = app (lam (\y -> y)) x

exEnv :: VEnv '[Int]
exEnv = (ECons (Identity 3) ENil)

example :: Int
example = runSTLC (runOpenSTLC term) 3
