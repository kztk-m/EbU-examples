{-

Example use of Embedding by Unembedding: the incremental language CTS, the cache
transfer style iteration on the incremental lambda calculus.

-}

{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE ExistentialQuantification  #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}

module Unembedding.Examples.CTS where

import           Data.Kind     (Type)
import           Prelude       hiding (concat, concatMap, map)

import           Data.Sequence (Seq, (><))
import qualified Data.Sequence as S

import qualified Control.Monad
import           Data.Foldable (toList)
import           Data.List     (foldl')
import           Data.Monoid   (Sum (Sum))
import           Unembedding.Env
import           Unembedding   (Dim (..), EnvI (..), Variables (..), ol0, ol1)
import qualified Unembedding   as UE

-- Change Structures:
-- A key part of incremental computation is representing changes in data.
-- This is done via change structures that consist of:
--   * The set you want to describe changes on, V
--   * The set that represents a diff, delta V
--   * A way to apply a diff, /+
--   * A way to work out a diff, /-

-- We focus on /+
-- We do this because we don't need minus for this example and omitting it keeps things simpler
-- We do not use minus as it is not used in out interp and it is hard / orthogonal
-- to compute differences

-- | Represents a diff on type a. We require a monoid as it is natural to do so
class Monoid (Delta a) => Diff a where
  -- | Type of diffs
  data Delta a :: Type

  -- Armed with /+ that repsects the monoidal properties of the diff
  -- prop> a /+ mempty == a
  -- prop> a /+ (da <> da') = a /+ da /+ da'
  (/+) :: a -> Delta a -> a

  checkEmpty :: Delta a -> Bool

-- Diffs on ():
-- Always empty

instance Semigroup (Delta ()) where
  _ <> _ = UnitDelta
instance Monoid (Delta ()) where
  mempty = UnitDelta

instance Diff () where
  data Delta () = UnitDelta
    deriving stock Show
  a /+ _ = a
  checkEmpty _ = True

-- Diffs on pairs:
-- Just pair together two diffs

instance (Semigroup (Delta a), Semigroup (Delta b)) => Semigroup (Delta (a, b)) where
  PairDelta dx1 dy1 <> PairDelta dx2 dy2 = PairDelta (dx1 <> dx2) (dy1 <> dy2)

instance (Monoid (Delta a), Monoid (Delta b)) => Monoid (Delta (a, b)) where
  mempty = PairDelta mempty mempty

instance (Diff a, Diff b) => Diff (a, b) where
  data Delta (a, b) = PairDelta (Delta a) (Delta b)
  (x, y) /+ PairDelta dx dy = (x /+ dx, y /+ dy)

  checkEmpty (PairDelta dx dy) = checkEmpty dx && checkEmpty dy

deriving stock instance (Show (Delta a) , Show (Delta b)) => Show (Delta (a, b))

-- Step 1: Identity semantic domain
-- -----------------------------------------------------------------------------

-- | Type wrapper about a type that can have a dif
data PackedDiff a where
  PackDiff :: Diff a => a -> PackedDiff a

-- | Type wrapper about a delta of a specific type
data PackedDiffDelta a where
  PackDiffDelta :: Diff a => Delta a -> PackedDiffDelta a

-- | Value environment
type VEnv = Env PackedDiff

-- | Delta env
type DEnv = Env PackedDiffDelta

-- | The semantic domain of a CTS expression
--   A CTS expression of type a in env consists of two things:
--     1. A way to get the result and the cache from a value env
--     2. A way to extract a delta on a with a cache from a delta env and a cache
data CTS env a = forall c. CTS (VEnv env -> (a, c))            -- Initializer
                               ((DEnv env, c) -> (Delta a, c)) -- Translator

instance Variables CTS where
  var = CTS (\(ECons (PackDiff x) _) -> (x, ()))
            (\(ECons (PackDiffDelta dx) _, _) -> (dx, ()))
  weaken (CTS f tr) = CTS f' tr'
    where
      f' (ECons _ e) = f e
      tr' (ECons _ de, c) = tr (de, c)

-- The purpose of this term is to be able to run a CTS term without the existentially qualified c
newtype Interact a b = I { runInteract :: a -> (b , Interact a b) }

-- for executing a CTS term
-- Takes a CTS term that expect one var in env, a value of that type and produces
-- the result along with how a change in a maps to a change in b, avoiding an existentially qualified c
runCTS :: Diff a => CTS '[a] b -> a -> (b, Interact (Delta a) (Delta b))
runCTS (CTS f tr) x =
  let e = ECons (PackDiff x) ENil -- make env containing just a
      (y, c0) = f e -- run term f with that env to yield a CTS thing
      -- remember CTS = (normal execution, maps diffs in env to diff in result)
      -- but we don't wanna have to deal with a c, so we use Interact
      -- h if a function that takes a cache an interaction between changes in a and changes in b
      h c = I $ \dx -> let (dy, c') = tr (ECons (PackDiffDelta dx) ENil, c) in (dy , h c')
  in (y, h c0)

-- Step 2: Prepare semantic functions for each construct
-- The constructs that we will support are:
--   * Unit
--   * pairing
--   * pair deconstruction (fst, snd)
--    * let clause (our binder)

unitSem :: CTS env ()
unitSem = CTS (const ((), ())) (const (UnitDelta, ()))

pairSem :: CTS env a -> CTS env b -> CTS env (a, b)
pairSem (CTS f1 tr1) (CTS f2 tr2) = CTS f' tr'
  where
    f' e =
        let (x, c1) = f1 e
            (y, c2) = f2 e
        in ( (x, y), (c1, c2) )
    tr' (de, (c1, c2)) =
      let (dx, c1') = tr1 (de, c1)
          (dy, c2') = tr2 (de, c2)
      in ( PairDelta dx dy, (c1', c2'))

fstSem :: CTS env (a, b) -> CTS env a
fstSem (CTS f tr) = CTS (\e -> let ((x,_), c) = f e in (x, c))
                        (\(de,c) -> let (PairDelta dx _, c') = tr (de, c) in (dx, c'))

sndSem :: CTS env (a, b) -> CTS env b
sndSem (CTS f tr) = CTS (\e -> let ((_,y), c) = f e in (y, c))
                        (\(de,c) -> let (PairDelta _ dy, c') = tr (de, c) in (dy, c'))

letSem :: Diff a => CTS env a -> CTS (a ': env) b -> CTS env b
letSem (CTS i1 tr1) (CTS i2 tr2) = CTS i tr
  where
    i e =
      let (x, c1) = i1 e -- Get x::a with i1.
          (y, c2) =
            i2 (ECons (PackDiff x) e) -- Get y::b with i2 on env with x added.
      in (y, (c1, c2)) -- Result, y, is returned with new cache.
    tr (de, (c1,c2)) = -- Same story but for incremental evaluation.
      let (dx, c1') = tr1 (de, c1)
          (dy, c2') = tr2 (ECons (PackDiffDelta dx) de, c2)
      in (dy, (c1', c2'))

-- Step 3: Provide HOAS rep of syntax
-- NOTE:- this is called CTSBase cos later we optimise to CTSSeq

class CTSBase exp where
  unit :: exp ()
  pair :: exp a -> exp b -> exp (a, b)
  fst_ :: exp (a, b) -> exp a
  snd_ :: exp (a, b) -> exp b
  let_ :: Diff a => exp a -> (exp a -> exp b) -> exp b

-- Step 4: Implement HOAS functions by lifting semantic functions

instance CTSBase (EnvI CTS) where
  unit = UE.liftFO0 unitSem
  pair = UE.liftFO2 pairSem
  fst_ = UE.liftFO1 fstSem
  snd_ = UE.liftFO1 sndSem
  let_ = UE.liftSOn (ol0 :. ol1 :. End) letSem

-- The language is now extended to support Sequences
-- To do this, we have the diff infrastructure for sequences, then another type
-- class to extend the syntax, with matching semantic functions
-- (basically we repeat the recipe for the extension)

-- diff infrastructure for sequences

instance Diff Int where
  newtype Delta Int = DInt (Sum Int)
    deriving newtype (Semigroup, Monoid)
  n /+ DInt (Sum dn) = n + dn

  checkEmpty (DInt (Sum n)) = n == 0

instance Show (Delta Int) where
  show (DInt (Sum n)) = "+" ++ show n

data ADSeq a = Ins Int a | Del Int | Rep Int (Delta a)

deriving stock instance (Show (Delta a), Show a) => Show (ADSeq a)

applyAtomicDelta :: Diff a => Seq a -> ADSeq a -> Seq a
applyAtomicDelta s (Ins i x) =
  let (s1, s2) = S.splitAt i s
  in s1 >< S.singleton x >< s2
applyAtomicDelta s (Del i) = S.deleteAt i s
applyAtomicDelta s (Rep i dx) =
  S.adjust' (/+ dx) i s

-- >>> applyAtomicDelta (S.fromList [0 :: Int]) (Ins 1 42)
-- fromList [0,42]

-- >>> applyAtomicDelta (S.fromList [S.fromList [0 :: Int], S.fromList [1]]) (Rep 0 (DSeq [Ins 1 42]))
-- fromList [fromList [0,42],fromList [1]]

instance Diff a => Diff (Seq a) where
  newtype Delta (Seq a) = DSeq [ADSeq a]
    deriving newtype (Semigroup, Monoid)
  s /+ (DSeq xds) = foldl' applyAtomicDelta s xds

  checkEmpty (DSeq ns) = null ns

deriving stock instance (Show a, Show (Delta a)) => Show (Delta (Seq a))

-- Constructs CTSBase gets extended with to support sequences
class CTSBase exp => CTSSeq exp where
  empty     :: exp (Seq a)
  singleton :: exp a -> exp (Seq a)
  concat    :: exp (Seq (Seq a)) -> exp (Seq a)
  map       :: (Diff a, Diff b) => (exp a -> exp b) -> exp (Seq a) -> exp (Seq b)
--  append    :: exp (Seq a) -> exp (Seq a) -> exp (Seq a)
  concatMap :: (Diff a, Diff b) => (exp a -> exp (Seq b)) -> exp (Seq a) -> exp (Seq b)

-- Semantics of lang extension

emptySem :: CTS env (Seq a)
emptySem = CTS (const (S.empty, ())) (const (DSeq [], ()))

singletonSem :: CTS env a -> CTS env (Seq a)
singletonSem (CTS f tr) =
  CTS (\e -> let (x, c) = f e in (S.singleton x, c))
      (\(de, c) -> let (dx, c') = tr (de, c) in (DSeq [Rep 0 dx], c') )


iterTr
  :: Monoid m
  => ((a, c) -> (m, c)) -- (value, cache) -> (monoid cache)
                        -- in this file it is used specifically go between a
                        -- ADSeq value and a Delta monoid
  -> (([a], c) -> (m, c)) -- this function upgrades this transformation to work on a [a]
-- works by using the monoid to crush the list
iterTr _ ([], c) = (mempty, c)
iterTr f (x : xs, c) =
  let (m1, c') = f (x, c)
      (m2, c'') = iterTr f (xs, c')
  in (m1 <> m2, c'')

concatSem :: CTS env (Seq (Seq a)) -> CTS env (Seq a)
concatSem (CTS f tr) = CTS f' tr'
  where
    f' e =
      let (ss, c) = f e
      in (Control.Monad.join ss, (c, fmap length ss))
                                -- (length of original list, length of baby lists)

    -- we need to change a seq of seq of changes to be a seq of changes
    -- this is a lot of index management
    -- :: (DEnv env, c) -> (Delta a, c)
    tr' (de, (c, cs)) = -- the c here is the cache of CTS env (Seq (Seq a)), which is existentially qualified
      let (DSeq dss, c') = tr (de, c) -- extract out the seq of seq of changes (dss)
          (ds, cs') = iterTr trAtomic (dss, cs) -- dss :: [ADSeq (Seq a)]
          -- iterTr :: Monoid m => ((a, c) -> (m, c)) -> (([a], c) -> (m, c))
          -- iterTr :: (ADSeq (Seq a), Seq Int) -> (Delta (Seq a), Seq Int)
      in (ds, (c',cs'))

    -- inserts an element into a seq at given index
    insAt :: Int -> a -> Seq a -> Seq a
    insAt i x s =
      let (s1, s2) = S.splitAt i s
      in s1 >< S.singleton x >< s2

    trAtomic :: (ADSeq (Seq a), Seq Int) -> (Delta (Seq a), Seq Int)
    trAtomic (Ins i xs, cs) =
      let toI = sum $ S.take i cs
          cs' = insAt i (S.length xs) cs
      in (DSeq $ reverse [Ins toI a | a <- toList xs ], cs')
    trAtomic (Del i, cs) =
      let (c1, c23) = S.splitAt i cs
          (c2, c3)  = S.splitAt 1 c23
          toI = sum c1
          toN = sum c2
      in (DSeq [Del toI | _ <- [1..toN] ], c1 >< c3 )
    trAtomic (Rep i (DSeq ds), cs)
      | Nothing <- S.lookup i cs = (mempty, cs)
      | Just ci <- S.lookup i cs =
        let offset   = sum $ S.take i cs
            (ds', ci') = iterTr (goAtomic offset) (ds, ci)
            cs' = S.update i ci' cs
        in (ds', cs')

    goAtomic :: Int -> (ADSeq a, Int) -> (Delta (Seq a), Int)
    goAtomic offset (Ins i x, ci) =
      let i' = min (max i 0) ci -- i must be [0, ci]
      in (DSeq $ pure $ Ins (offset + i') x, ci + 1)
    goAtomic offset (Del i, ci) =
      let i' = min (max i 0) (ci - 1)
      in (DSeq $ pure $ Del (offset + i'), ci - 1)
    goAtomic offset (Rep i dx, ci)
      | i < 0 || i >= ci = (mempty, ci)
      | otherwise        = (DSeq $ pure $ Rep (offset + i) dx, ci)

-- letSem is used to make this def simpler as it reduced the amount of arguments
-- by putting e2 (xs) into the environment
mapSem :: (Diff a, Diff b) =>
          CTS (a : env) b -> CTS env (Seq a) -> CTS env (Seq b)
mapSem e1 e2 = letSem e2 (mapSem' e1)

-- NOTE:- that the comments ignore the cache and just track the values and diffs
-- now we have something that knows what to do with as, and we have to turn out
-- Seq a that is in our env into a Seq b
mapSem' :: (Diff a, Diff b) => CTS (a ': env) b -> CTS (Seq a ': env) (Seq b)
mapSem' (CTS f tr) = CTS f' tr'
  where
    -- (VEnv (Seq a ': env) -> (Seq b, _))
    f' (ECons (PackDiff xs) e) = -- we pattern match on the sequence to get it out
      -- now we wanna apply f to each elem
      -- f works by expecting the value in its env
      -- so we make a wrapper function that puts the value there
      let h x = f (ECons (PackDiff x) e)
          (ys, cs) = S.unzip (fmap h xs) -- then map that function
      in (ys, (cs, h))

    -- we pattern match again to deal with dxs :: Seq a and de :: DEnv env
    -- transArg deals with dxs
    -- transEnv deals with env
    tr' (ECons (PackDiffDelta dxs) de, (cs, h)) =
      let deEmpty = mapEnv (\(PackDiffDelta _) -> PackDiffDelta mempty) de
          htr (dx, c) = tr (ECons (PackDiffDelta dx) deEmpty, c)
          dh c        = tr (ECons (PackDiffDelta mempty) de, c)
          (dys1, cs1) = transArg h htr (dxs, cs) -- dxs :: Delta (Seq a) = DSeq [ADSeq a]
          (dys2, cs2) = transEnv dh cs1
          h' a = let (b, c) = h a; (dy, c') = dh c in (b /+ dy, c')
          --  having dealt with dxs and env separately, we compose with monoid
      in (dys1 <> dys2, (cs2, h'))

    -- the changes we get from Seq a
    transArg h htr (DSeq adxs, cs) = iterTr (transArgAtom h htr) (adxs, cs)
      -- adxs :: [ADSeq a] (list of the ADT with ins del and rep)

    -- :: (ADSeq a, c) -> Delta (Seq b)
    --                    DSeq [ADSeq b]
    transArgAtom h _htr (Ins i x, cs) =
      let (y, c) = h x -- get the y::b
      in (DSeq $ pure $ Ins i y, S.insertAt i c cs) -- wrap in require type, dealing with cache
    transArgAtom _h _htr (Del i, cs) =
      (DSeq $ pure $ Del i, S.deleteAt i cs) -- no as, so just wrap
    transArgAtom _h htr (Rep i dx, cs) =
      let ci = S.index cs i
          (dy, ci') = htr (dx, ci)  -- change dx to dy
      in (rep i dy, S.update i ci' cs) -- package

    -- dh is this: dh c = tr (ECons (PackDiffDelta mempty) denv, c)
    -- it uses the old function that changes as to bs with empty changes
    -- dh :: a -> (Delta b, b1)
    -- cs is an original cache thing
    transEnv dh cs =
      let (dys, cs') = S.unzip (fmap dh cs)
      in (mconcat $ zipWith rep [0..] (toList dys), cs')

rep :: Diff a => Int -> Delta a -> Delta (Seq a)
rep i dx | checkEmpty dx = mempty
         | otherwise     = DSeq [ Rep i dx ]

-- lifting semantics

instance CTSSeq (EnvI CTS) where
  empty     = UE.liftFO0 emptySem
  singleton = UE.liftFO1 singletonSem
  concat    = UE.liftFO1 concatSem
  map       = UE.liftSOn (ol1 :. ol0 :. End) mapSem
  concatMap = UE.liftSOn (ol1 :. ol0 :. End) (\f x -> concatSem $ mapSem f x )

-- Now armed with the features for a more interesting example, we interpret open
-- expressions using UE.runOpen

cartesianRecreation :: (CTSSeq exp, Diff a, Diff b)
                    => exp (Seq a) -> exp (Seq b) -> exp (Seq (a, b))
cartesianRecreation xs ys = concatMap (\x -> map (\y -> pair x y) ys) xs

caInc :: (Diff a, Diff b) => (Seq a, Seq b) -> (Seq (a,b), Interact (Delta (Seq a, Seq b)) (Delta (Seq (a,b))))
caInc = runCTS $ UE.runOpen $ \zs -> cartesianRecreation (Unembedding.Examples.CTS.fst_ zs) (Unembedding.Examples.CTS.snd_ zs)

-- >>> let (r, i) = caInc (S.fromList [1..10 :: Int], S.fromList [1..10 :: Int])
-- >>> r
-- fromList [(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9),(1,10),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(2,9),(2,10),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),(3,8),(3,9),(3,10),(4,1),(4,2),(4,3),(4,4),(4,5),(4,6),(4,7),(4,8),(4,9),(4,10),(5,1),(5,2),(5,3),(5,4),(5,5),(5,6),(5,7),(5,8),(5,9),(5,10),(6,1),(6,2),(6,3),(6,4),(6,5),(6,6),(6,7),(6,8),(6,9),(6,10),(7,1),(7,2),(7,3),(7,4),(7,5),(7,6),(7,7),(7,8),(7,9),(7,10),(8,1),(8,2),(8,3),(8,4),(8,5),(8,6),(8,7),(8,8),(8,9),(8,10),(9,1),(9,2),(9,3),(9,4),(9,5),(9,6),(9,7),(9,8),(9,9),(9,10),(10,1),(10,2),(10,3),(10,4),(10,5),(10,6),(10,7),(10,8),(10,9),(10,10)]
-- >>> let (d1, i1) = runInteract i (PairDelta (DSeq [Ins 0 20]) mempty)
-- >>> d1
-- DSeq [Ins 0 (20,10),Ins 0 (20,9),Ins 0 (20,8),Ins 0 (20,7),Ins 0 (20,6),Ins 0 (20,5),Ins 0 (20,4),Ins 0 (20,3),Ins 0 (20,2),Ins 0 (20,1)]
