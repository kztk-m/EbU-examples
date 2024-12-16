{-

Lens code for paper

-}

{-# LANGUAGE ConstraintKinds           #-}
{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE DerivingStrategies        #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE FunctionalDependencies    #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE PatternSynonyms           #-}
{-# LANGUAGE PolyKinds                 #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeFamilyDependencies    #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Unembedding.Examples.AppLens where

-- base
import           Data.Maybe  (fromMaybe)
import           Data.Proxy  (Proxy (..))
import           Prelude     hiding (LT)

-- unembedding tooling
import           Unembedding.Env
import           Unembedding (Dim (..), EnvI (..), TEnv, Variables (..), ol0)
import qualified Unembedding as UE

-- Step 1: Identity semantic domain
-- -----------------------------------------------------------------------------

-- type
newtype LensTerm env a = LT {runLT :: TEnv env -> Lens (VEnv env) a}
type VEnv = Env Maybe
data Lens s v = L {get :: s -> v, put :: s -> v -> s}

-- var instance

instance Variables LensTerm where
  var = LT $ \(ECons _ e) ->
    L (\(ECons (Just a) _) -> a)           -- get
      (\_ a -> ECons (Just a) (unitEnv e)) -- put
  weaken t = LT $ \(ECons _ e) ->
    let l = runLT t e
    in L (\(ECons _ env) -> get l env)               -- get
         (\(ECons b env) a -> ECons b (put l env a)) -- put

-- Step 2: Prepare semantic functions for each construct
-- -----------------------------------------------------------------------------

-- the lenses do all the work, we are writing lenses over the envs, which do the shuffling
-- then get packed up as terms

unpairSem :: LensTerm env (a, b) -> LensTerm (a ': b ': env) r -> LensTerm env r
unpairSem t1 t2 = LT $ \e ->
  let l1 = runLT t1 e
      l2 = runLT t2 (ECons Proxy (ECons Proxy e))
  in letLens l1 (rearrPair l2)

rearrPair :: Lens (VEnv (a ': b ': env)) r -> Lens (VEnv ((a, b) ': env)) r
rearrPair l = L g p
  where
    g (ECons (Just (a, b)) env) = get l (ECons (Just a) (ECons (Just b) env))
    p (ECons (Just (a, b)) env) r =
      let ECons m (ECons n env') = put l (ECons (Just a) (ECons (Just b) env)) r
      in ECons (Just (fromMaybe a m, fromMaybe b n)) env'

letLens :: Lens (VEnv env) a -> Lens (VEnv (a ': env)) b -> Lens (VEnv env) b
letLens l1 l2 = L g p
  where
    g env = get l2 (ECons (Just (get l1 env)) env)
    p env b = let a = get l1 env
                  ECons m env1' = put l2 (ECons (Just a) env) b
                  env2' = put l1 env (fromMaybe a m)
              in merge env1' env2'

letSem :: LensTerm env a -> LensTerm (a : env) b -> LensTerm env b
letSem t1 t2 = LT $ \e -> letLens (runLT t1 e) (runLT t2 (ECons Proxy e))

merge :: VEnv env -> VEnv env -> VEnv env
merge = undefined

unitEnv :: TEnv env -> VEnv env
unitEnv ENil        = ENil
unitEnv (ECons _ e) = ECons Nothing (unitEnv e)

-- Step 3: Provide HOAS rep of syntax
-- -----------------------------------------------------------------------------

class AppLens exp where
  prim :: Lens a b -> exp a -> exp b
  unit :: exp ()
  pair :: exp a -> exp b -> exp (a,b)

class AppLens exp => AppLensUnpair exp where
  unpair :: exp (a, b) -> (exp a -> exp b -> exp r) -> exp r

-- Step 4: Implement HOAS functions by lifting semantic functions
-- -----------------------------------------------------------------------------

-- instance with lifting
