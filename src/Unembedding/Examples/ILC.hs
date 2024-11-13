{-

An unembedded implementation of the Incremental Lambda Calc.
(https://inc-lc.github.io/resources/pldi14-ilc-author-final.pdf)

This is a simpler version than CTS, which embeds the successor of ICL, using
cache transfer style

-}

{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Unembedding.Examples.ILC where

-- base
import           Control.Monad            (join)
import           Data.Foldable            (toList)

-- containers
import           Data.Sequence            (Seq)
import qualified Data.Sequence            as S

-- unembedding tooling
import qualified Unembedding              as UE
import           Unembedding              (Dim (..), EnvI (..), LiftVariables,
                                           Variables (..), ol0, ol1)
import           Unembedding.Env

-- We will reuse the change structure from CTS.
import           Unembedding.Examples.CTS (ADSeq (..), DEnv, Delta (..),
                                           Diff (..), PackedDiff (..),
                                           PackedDiffDelta (..), VEnv)

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

-- | The semantic domain of an ILC expression with type a and environment env.
--   Expressions in ILC should be able to be interpreted in two ways:
--     1. Using standard evaluation, where variable assignments map to results
--     2. Using differential evaluation, where inputs and input differences are mapped to a
--        change in the output
data ILC env a = Inc
  { sEval :: VEnv env -> a, dEval :: VEnv env -> DEnv env -> Delta a }

-- Since both parts of this semantics features an environment, it is easy to see
-- that it is a member of the Variables type class.
-- (the type class just insists that there is a way to reference a variable in context,
--  and a way to weaken that context. Featuring environments provides this)

instance Variables ILC where
  var :: ILC (a : as) a
  var = Inc (\  (ECons (PackDiff a) _) -> a)
            (\_ (ECons (PackDiffDelta da) _) -> da)
  weaken :: ILC as a -> ILC (b : as) a
  weaken (Inc s d) = Inc s' d'
    where
      s' (ECons _ env) = s env
      d' (ECons _ venv) (ECons _ denv) = d venv denv

instance LiftVariables ILC ILC where
  liftVar = id

-- Step 2: Prepare semantic functions for each construct
-- -----------------------------------------------------------------------------
-- The constructs that we will support are:
--   * Unit
--   * pairing
--   * pair deconstruction (fst, snd)
--   * let clause (our binder)

unitSem :: ILC env ()
unitSem = Inc (const ()) (\_ _ -> UnitDelta)

pairSem :: ILC env a -> ILC env b -> ILC env (a, b)
pairSem x y = Inc (\e -> (sEval x e, sEval y e)) -- pair results together either using (,) or PairDelta
                  (\venv denv -> PairDelta (dEval x venv denv) (dEval y venv denv))

fstSem :: ILC env (a, b) -> ILC env a
fstSem (Inc s d) = Inc (fst . s) -- take fst of result
                       (\venv denv -> let (PairDelta x _) = d venv denv in x)
                        -- run f to get paired delta, then take first part of it

sndSem :: ILC env (a, b) -> ILC env b
sndSem (Inc s d) = Inc (snd . s) -- take snd of result
                       (\venv denv -> let (PairDelta _ y) = d venv denv in y)
                      -- run f to get paired delta, then take second part of it

-- let_ :: Diff a => e a -> (e a -> e b) -> e b
letSem :: Diff a => ILC env a -> ILC (a ': env) b -> ILC env b
letSem (Inc sa da) (Inc sb db)
  = Inc (\e ->
          let x = sa e                  -- unpack a
              e' = ECons (PackDiff x) e -- add a to env
          in sb e'                      -- extract b with new env
        )
        (\ve de ->
          let x = sa ve                          -- unpack a
              e' = ECons (PackDiff x) ve         -- add a to env
              da' = da ve de                     -- unpack da
              de' = ECons (PackDiffDelta da') de -- add da to env
          in db e' de'                           -- extract b with new env
        )

-- Step 3: Provide HOAS rep of syntax
-- -----------------------------------------------------------------------------

-- this is just the same as CTSBase, but I'll copy it and rename it
class ILChoas exp where
  unit :: exp ()
  pair :: exp a -> exp b -> exp (a, b)
  fst_ :: exp (a, b) -> exp a
  snd_ :: exp (a, b) -> exp b
  let_ :: Diff a => exp a -> (exp a -> exp b) -> exp b

-- Step 4: Implement HOAS functions by lifting semantic functions
-- -----------------------------------------------------------------------------

-- again identical to CTS's instance of CTSBase modulo renaming
instance ILChoas (EnvI ILC) where
  -- constructs without binders => we use liftFO
  unit = UE.liftFO0 unitSem -- 0 args => 0
  pair = UE.liftFO2 pairSem -- 2 args => 2
  fst_ = UE.liftFO1 fstSem  -- 1 arg  => 1
  snd_ = UE.liftFO1 sndSem
  -- our binding construct => we use listSO
  let_ = UE.liftSOn (ol0 :. ol1 :. End) letSem

-- Now you can interpret open expressions if you want
-- -----------------------------------------------------------------------------

-- Unlike CTS, we don't need an Interact type as there is not existentially
-- qualified type to deal with

-- | Runs a ICL term that only expects one var in the env
runILC :: Diff a => ILC '[a] b -> a -> (b, Delta a -> Delta b)
runILC t x = let
    ve = ECons (PackDiff x) ENil
    r = sEval t ve
    f da = let de = ECons (PackDiffDelta da) ENil
           in dEval t ve de
    in (r, f)

-- example ILC term (without binding):
termICL :: ILC '[Int] (Int, Int)
termICL = UE.runOpen termICL'
  where
    termICL' :: EnvI ILC Int -> EnvI ILC (Int, Int)
    termICL' x = pair x x

-- >>> fst $ runILC termICL 5
-- (5,5)
-- >>> (snd $ runILC termICL 5) (DInt 1)
-- PairDelta +1 +1

-- example ILC term (binding):
termICLb :: ILC '[(Int,Int)] (Int, Int)
termICLb = UE.runOpen term

term :: EnvI ILC (Int, Int) -> EnvI ILC (Int, Int)
term x = let_ (fst_ x) (\y -> pair y y)
-- takes in a tuple, takes the first elem, and pairs it with itself

-- >>> fst $ runILC termICLb (7,6)
-- (7,7)
-- >>> (snd $ runILC termICLb (7,6)) (PairDelta (DInt 3) (DInt 2))
-- PairDelta +3 +3

-- Seq language extension
-- -----------------------------------------------------------------------------
-- We will show adding sequences to ILC to redo the recipe again to solidify what
-- is going on in the readers' mind and show that unembedding is an extensible technique.

-- NOTE:- there is an existing issue with ILC that it is only efficient when the
-- derivative is _self-maintainable_, that is computations whose output changes
-- can be computed using only input changes, but not the inputs themselves.
-- When they are not, this reverts us to recompilation.
-- For more details see
-- the CTS paper, section 2.1 where they demonstrate this with an example

-- When adding new constructs to the language, you just replay part of the recipe
-- You dont need to do step one again, but you need to do 2,3 and 4 for your new additions

-- For this extension we will add constructs to support sequences:
--  empty, singleton, concat, map

-- We will also need diff structure for sequences (which we have already done in CTS.hs)

-- Seq for speeeeddd cos incremental

-- 2. Prepare semantic functions for each construct

emptySem :: ILC env (Seq a)
emptySem = Inc
  (const S.empty)   -- const the empty sequence
  (\_ _ -> DSeq []) -- const the empty change on sequences

singletonSem :: ILC env a -> ILC env (Seq a)
concatSem    :: ILC env (Seq (Seq a)) -> ILC env (Seq a)
mapSem :: (Diff a, Diff b)
       => ILC (a : env) b -> ILC env (Seq a) -> ILC env (Seq b)

singletonSem x = Inc
  (S.singleton . sEval x) -- get the a value, and bung it in a sequence
  (\ve de -> let da = dEval x ve de in DSeq [Rep 0 da] )
  -- converting a change on an a to a change on the singleton sequence is extracting
  -- the change on a (da) and creating the sequence change that represent making that
  -- change to the first element of the sequence

concatSem xss = Inc
  (join . sEval xss) -- get the value and concat it
  deval'
  where
    -- :: VEnv env -> DEnv env -> Delta (Seq a)
    deval' venv denv = f (makeCache $ sEval xss venv) (dEval xss venv denv)

    f :: Seq Int -> Delta (Seq (Seq a)) -> Delta (Seq a)
    f c0 (DSeq dxss) = fst $ foldr (\da (dxs, c) -> let (dxs', c') = transOuterChange c da in (dxs <> dxs', c')) (mempty, c0) dxss

    -- We do not need the whole input; the length of each inner list is enough for change propagation.
    -- We call the data `cache`, analogously to the cache-transfer version.
    makeCache :: Seq (Seq a) -> Seq Int
    makeCache = fmap S.length

    transOuterChange :: Seq Int -> ADSeq (Seq a) -> (Delta (Seq a), Seq Int)
    transOuterChange lengths (Ins i ys) =
      -- insertion of a sequence ys to the ith element
      -- ===> insertion of ys to the i'th element, where i' = len_1 + ... len_(i - 1)
      --      = repeated insertion of b_k to the i'th element (k = len ys ... 1).
      let (lengths_before_i, lengths_rest) = S.splitAt i lengths
          i'        = sum lengths_before_i
          lengths' = lengths_before_i S.>< S.singleton (S.length ys) S.>< lengths_rest
      in (DSeq $ reverse [Ins i' e | e <- toList ys ], lengths')
    transOuterChange lengths (Del i) =
      -- deletion the ith element from an input list (which must be a sequence of length len_i)
      -- ===> deletion of the i'th to (i'+n) elements, where i' = len_1 + ... len_(i - 1) and n = len_i.
      --      = n-time deletion of the i'th element.
      let (lengths_before_i, lengths_rest) = S.splitAt i lengths
          (len_i, lengths_after_i)         = S.splitAt 1 lengths_rest
          i' = sum lengths_before_i
          n = sum len_i
      in (DSeq [Del i' | _ <- [1..n] ], lengths_before_i S.>< lengths_after_i )
    transOuterChange lengths (Rep i (DSeq dxs))
      | Nothing    <- S.lookup i lengths =
        -- Corner Case: 'Rep i da' does nothing if i is not a valid index.
        (mempty, lengths)
      | Just len_i <- S.lookup i lengths =
        -- update to jth element of the ith inner list
        -- ===> update to j'th element where j' = j + len_1 + ... + len_(i - 1)
        let offset = sum $ S.take i lengths -- offset = len_1 + ... + len_(i-1)
            (dxs',len_i') = foldr (\da (d_res, l) -> let (d_res', l') = transInnerChange offset l da in (d_res <> d_res', l')) (mempty, len_i) dxs
        in (dxs', S.update i len_i' lengths)

    clamp :: Ord a => a -> a -> a -> a
    clamp v lowerCap upperCap
      | lowerCap > upperCap = clamp v upperCap lowerCap
      | otherwise     = min (max v lowerCap) upperCap

    -- Translating updates on the jth element to that on the (j + offset)th element, with normalization
    transInnerChange :: Int -> Int -> ADSeq a -> (Delta (Seq a), Int)
    transInnerChange offset len (Ins pre_j a)  =
      let -- normalize j: 'Ins i a' and 'Ins (normalize i 0 len) a' have the same effect when it is applied to a sequence of length len.
          j = clamp pre_j 0 len
      in (DSeq $ pure $ Ins (offset + j) a, len + 1)
    transInnerChange offset len (Del pre_j)    =
      let -- normalize j: 'Del i' and 'Del (normalize i 0 (len - 1)' have the same effect when it is applied to a sequence of length len.
          j = clamp pre_j 0 (len - 1)
      in (DSeq $ pure $ Del (offset + j), len + 1)
    transInnerChange offset len (Rep j da)
      | 0 < j || j >= len = -- Corner Case: 'Rep i da' does nothing if i is not a valid index.
        (mempty, len)
      | otherwise =
        (DSeq $ pure $ Rep (offset + j) da, len)

mapSem f xs = letSem xs (mapSem' f)
  -- letSem is used to make this def simpler, as it reduces the amount of arguments
  -- by putting xs into the environment

mapSem' :: (Diff a, Diff b) => ILC (a : env) b -> ILC (Seq a : env) (Seq b)
mapSem' _f@(Inc sf df) = Inc sEnv' dEnv'
  where
    -- apply the standard evaluation of f (sf) to each value in the sequence
    sEnv' (ECons (PackDiff xs) e) -- unpack the sequence xs by pattern matching
      = let
        h x = sf (ECons (PackDiff x) e) -- make wrapper function for application of sf
        ys = fmap h xs                  -- map wrapper function over xs
        in ys

    -- Convert any delta xs to become delta ys
    -- :: VEnv (Seq a : env) -> DEnv (Seq a : env) -> Delta (Seq b)
    dEnv' (ECons (PackDiff xs) e) (ECons (PackDiffDelta dxs) de) =
      -- to break down the problem,
      -- we pattern match to deal with dxs :: Seq a and de :: DEnv separately,
      -- and compose together at the end using the monoid
      let -- changes from Seq a
          -- each of the delta xs (dxs) needs changed to be delta b (dys1)
          -- dxs :: Delta (Seq a) ~ DSeq [ADSeq a]
          -- to this Delta (Seq a) into a Delta (Seq a), we unpack the [ADSeq a]
          -- and use the function iterTr to walk the list converting each ADSeq a
          -- to a delta b and using the delta b monoid to combine the results together
          -- into one delta b
          dys1 = transArg dxs
          transArg (DSeq adxs) = iterTr transArgAtom adxs
          transArgAtom (Ins i a)  = DSeq [Ins i (xsTOys a)]
          transArgAtom (Del i)    = DSeq [Del i]
          transArgAtom (Rep i da) = DSeq [Rep i (dxsTOdys i da)]
          -- To help us do this, we need a function to convert xs to ys and a function
          -- to convert delta xs to delta ys, we get these from f's standard eval
          -- and deval respectively
          -- wrapper functions seval and deval from f:
          xsTOys a = sf (ECons (PackDiff a) e) -- wrapper function for application of sf, turns as to ys
          dxsTOdys i da = df (ECons (PackDiff (S.index xs i /+ da)) e) (ECons (PackDiffDelta da) deEmpty) -- wrapper function for application of df, turns das to dys
          -- dxsTOdys uses an empty environment (deEmpty) so we can focus on Seq a
          -- (no empty version of the venv cos that doesnt make sense)
          deEmpty = mapEnv (\(PackDiffDelta _) -> PackDiffDelta mempty) de

          -- changes from env
          xs' = xs /+ dxs -- NOTE:- re-computation!
          dys2 = mconcat $ zipWith rep [0..] $ fmap uf (toList xs')
          uf a = df (ECons (PackDiff a) e) (ECons (PackDiffDelta mempty) de)
       -- compose deltas from Seq a and env together
      in dys1 <> dys2

rep :: Diff a => Int -> Delta a -> Delta (Seq a)
rep i da | checkEmpty da = mempty
         | otherwise     = DSeq [ Rep i da ]

-- monoid homo with help
iterTr
  :: Monoid m
  => (a -> m)
  -> ([a] -> m)
iterTr f xs = mconcat $ fmap f xs

-- 3. Provide HOAS rep of syntax

-- Same as CTSSeq, but copied and renamed
-- nice little sub class
class ILChoas exp => ILCSeq exp where
  empty     :: exp (Seq a)
  singleton :: exp a -> exp (Seq a)
  concat    :: exp (Seq (Seq a)) -> exp (Seq a)
  map :: (Diff a, Diff b) => (exp a -> exp b) -> exp (Seq a) -> exp (Seq b)

-- 4. Implement HOAS functions by lifting semantic functions

instance ILCSeq (EnvI ILC) where
  empty     = UE.liftFO0 emptySem
  singleton = UE.liftFO1 singletonSem
  concat    = UE.liftFO1 concatSem
  map       = UE.liftSOn (ol1 :. ol0 :. End) mapSem


-- testing concat
-- >>> let (r, i) = (runILC $ UE.runOpen Examples.ILC.concat) (S.fromList [ S.fromList [1,2 :: Int], S.fromList [3], S.fromList [4,5,6] ])
-- >>> r
-- fromList [1,2,3,4,5,6]
-- >>> let d1 = i (DSeq [Ins 3 (S.fromList [7,8])])
-- >>> d1
-- DSeq [Ins 6 8,Ins 6 7]
-- >>> r /+ d1
-- fromList [1,2,3,4,5,6,7,8]

cartesian :: (ILCSeq e, Diff a, Diff b)  => e (Seq a) -> e (Seq b) -> e (Seq (a, b))
cartesian xs ys = Unembedding.Examples.ILC.concat (Unembedding.Examples.ILC.map (\x -> Unembedding.Examples.ILC.map (\y -> pair x y) ys) xs)

caInc :: (Diff a, Diff b) => (Seq a, Seq b) -> (Seq (a,b), Delta (Seq a, Seq b) -> Delta (Seq (a, b)))-- , Interact (Delta (Seq a, Seq b)) (Delta (Seq (a,b))))
caInc = runILC $ UE.runOpen $ \zs -> cartesian (fst_ zs) (snd_ zs)

-- >>> let (r, i) = caInc (S.fromList [1..10 :: Int], S.fromList [1..10 :: Int])
-- >>> r
-- fromList [(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9),(1,10),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(2,9),(2,10),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),(3,8),(3,9),(3,10),(4,1),(4,2),(4,3),(4,4),(4,5),(4,6),(4,7),(4,8),(4,9),(4,10),(5,1),(5,2),(5,3),(5,4),(5,5),(5,6),(5,7),(5,8),(5,9),(5,10),(6,1),(6,2),(6,3),(6,4),(6,5),(6,6),(6,7),(6,8),(6,9),(6,10),(7,1),(7,2),(7,3),(7,4),(7,5),(7,6),(7,7),(7,8),(7,9),(7,10),(8,1),(8,2),(8,3),(8,4),(8,5),(8,6),(8,7),(8,8),(8,9),(8,10),(9,1),(9,2),(9,3),(9,4),(9,5),(9,6),(9,7),(9,8),(9,9),(9,10),(10,1),(10,2),(10,3),(10,4),(10,5),(10,6),(10,7),(10,8),(10,9),(10,10)]
-- >>> let d1 = i (PairDelta (DSeq [Ins 0 20]) mempty)
-- >>> d1
-- DSeq [Ins 0 (20,10),Ins 0 (20,9),Ins 0 (20,8),Ins 0 (20,7),Ins 0 (20,6),Ins 0 (20,5),Ins 0 (20,4),Ins 0 (20,3),Ins 0 (20,2),Ins 0 (20,1)]
-- >>> let d2 = i (PairDelta mempty (DSeq [Ins 0 20]))
-- >>> d2
-- DSeq [Ins 90 (10,20),Ins 80 (9,20),Ins 70 (8,20),Ins 60 (7,20),Ins 50 (6,20),Ins 40 (5,20),Ins 30 (4,20),Ins 20 (3,20),Ins 10 (2,20),Ins 0 (1,20)]

-- version without concat
-- just to check that map is right and it is
cartesian' :: (ILCSeq e, Diff a, Diff b)  => e (Seq a) -> e (Seq b) -> e (Seq (Seq (a, b)))
cartesian' xs ys = Unembedding.Examples.ILC.map (\x -> Unembedding.Examples.ILC.map (\y -> pair x y) ys) xs

caInc' :: (Diff a, Diff b) => (Seq a, Seq b) -> (Seq (Seq (a, b)), Delta (Seq a, Seq b) -> Delta (Seq (Seq (a, b))))-- , Interact (Delta (Seq a, Seq b)) (Delta (Seq (a,b))))
caInc' = runILC $ UE.runOpen $ \zs -> cartesian' (fst_ zs) (snd_ zs)

-- >>> let (r, i) = caInc' (S.fromList [1..10 :: Int], S.fromList [1..10 :: Int])
-- >>> r
-- fromList [fromList [(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9),(1,10)],fromList [(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(2,9),(2,10)],fromList [(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),(3,8),(3,9),(3,10)],fromList [(4,1),(4,2),(4,3),(4,4),(4,5),(4,6),(4,7),(4,8),(4,9),(4,10)],fromList [(5,1),(5,2),(5,3),(5,4),(5,5),(5,6),(5,7),(5,8),(5,9),(5,10)],fromList [(6,1),(6,2),(6,3),(6,4),(6,5),(6,6),(6,7),(6,8),(6,9),(6,10)],fromList [(7,1),(7,2),(7,3),(7,4),(7,5),(7,6),(7,7),(7,8),(7,9),(7,10)],fromList [(8,1),(8,2),(8,3),(8,4),(8,5),(8,6),(8,7),(8,8),(8,9),(8,10)],fromList [(9,1),(9,2),(9,3),(9,4),(9,5),(9,6),(9,7),(9,8),(9,9),(9,10)],fromList [(10,1),(10,2),(10,3),(10,4),(10,5),(10,6),(10,7),(10,8),(10,9),(10,10)]]
-- >>> let d1 = i (PairDelta (DSeq [Ins 0 20]) mempty)
-- >>> d1
-- DSeq [Ins 0 (fromList [(20,1),(20,2),(20,3),(20,4),(20,5),(20,6),(20,7),(20,8),(20,9),(20,10)])]
-- >>> let d2 = i (PairDelta mempty (DSeq [Ins 0 20]))
-- >>> d2
-- DSeq [Rep 0 (DSeq [Ins 0 (1,20)]),Rep 1 (DSeq [Ins 0 (2,20)]),Rep 2 (DSeq [Ins 0 (3,20)]),Rep 3 (DSeq [Ins 0 (4,20)]),Rep 4 (DSeq [Ins 0 (5,20)]),Rep 5 (DSeq [Ins 0 (6,20)]),Rep 6 (DSeq [Ins 0 (7,20)]),Rep 7 (DSeq [Ins 0 (8,20)]),Rep 8 (DSeq [Ins 0 (9,20)]),Rep 9 (DSeq [Ins 0 (10,20)])]
