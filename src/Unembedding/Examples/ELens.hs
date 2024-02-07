{-

Example use of Embedding by Unembedding: the lens language HOBiT.

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
{-# LANGUAGE ViewPatterns              #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}

module Unembedding.Examples.ELens where

import           Control.Category
import           Control.Monad.Except
import           Control.Monad.Identity (Identity (Identity))
import qualified Control.Monad.State    as State
import           Data.Coerce            (coerce)
import           Data.Either            (fromRight)
import qualified Data.Foldable
import           Data.Kind              (Type)
import           Data.Proxy             (Proxy (Proxy))
import           Prelude                hiding (LT, id, (.))
import           Unembedding.Env
import           Unembedding            (Dim (..), EnvI (..), OfLength (..),
                                         Repeat, SNat (..), Sig2 (..), TEnv,
                                         TermRep (..), URep (..),
                                         Variables (..), Vec (..))
import qualified Unembedding            as UE

type Err = Either String

newtype Lens a b = L { runLens :: a -> Err (b, b -> Err a) }


get :: Lens a b -> a -> Err b
get l = fmap fst . runLens l

put :: Lens a b -> a -> b -> Err a
put l s v = do
  (_, r) <- runLens l s
  r v

instance Category Lens where
  id = L $ \x -> pure (x, pure)

  L f2 . L f1 = L $ \x -> do
    (y, ry) <- f1 x
    (z, rz) <- f2 y
    pure (z, rz >=> ry)

data Used a = Used a | Unused
  deriving stock (Eq, Ord, Show)

data VEnv as where
  VNil   :: VEnv '[]
  VUndet :: VEnv as
  VCons  :: Used a -> VEnv as -> VEnv (a ': as)

unitL :: Lens (VEnv as) ()
unitL = L $ const $ pure ((), const $ pure VUndet)

dupL :: Lens (VEnv as) (VEnv as, VEnv as)
dupL = L $ \x -> pure ( (x, x), uncurry mergeEnv)

prodL :: Lens a1 b1 -> Lens a2 b2 -> Lens (a1, a2) (b1, b2)
prodL l1 l2 = L $ \(a1, a2) -> do
  (b1, r1) <- runLens l1 a1
  (b2, r2) <- runLens l2 a2
  pure ((b1, b2), \(b1',b2') -> (,) <$> r1 b1' <*> r2 b2')

splitL :: Lens (VEnv as) a -> Lens (VEnv as) b -> Lens (VEnv as) (a, b)
splitL f g = prodL f g . dupL

mergeEnv :: VEnv as -> VEnv as -> Err (VEnv as)
mergeEnv VNil   _ = pure VNil
mergeEnv VUndet v = pure v
mergeEnv (VCons v1 vs1) VUndet = pure $ VCons v1 vs1
mergeEnv (VCons v1 vs1) (VCons v2 vs2) =
  case (v1, v2) of
    (Unused, v)      -> VCons v        <$> mergeEnv vs1 vs2
    (Used v, Unused) -> VCons (Used v) <$> mergeEnv vs1 vs2
    _                -> throwError "runtime linearity checking failed: some variables used more than once"

msgViolatedMaximalityAssumption :: String
msgViolatedMaximalityAssumption = "violated assumption on the original source: all inputs must be present."




weakenLens :: Lens (VEnv as) b -> Lens (VEnv (a ': as)) b
weakenLens l = L $ \case
    VCons (Used _) venv' -> do
      (y, r) <- runLens l venv'
      pure (y, fmap (VCons Unused) . r)
    _ -> throwError $ "weakenLens: " ++ msgViolatedMaximalityAssumption

varLens :: Lens (VEnv (a : as)) a
varLens = L $ \case
  VCons (Used x) _ -> pure (x, \x' -> pure (VCons (Used x') VUndet))
  _                -> throwError $ "varLens: " ++ msgViolatedMaximalityAssumption

newtype LensT as a = LT { unLensT :: Lens (VEnv as) a }

splitLT :: forall as a b . LensT as a -> LensT as b -> LensT as (a, b)
splitLT = coerce (splitL :: Lens (VEnv as) a -> Lens (VEnv as) b -> Lens (VEnv as) (a, b))

instance Variables LensT where
  var = LT varLens
  weaken (LT l) = LT $ weakenLens l

unLensTdot :: (forall as. TEnv as -> LensT as a ) -> (forall as. TEnv as -> Lens (VEnv as) a)
unLensTdot f e = unLensT (f e)

pattern ULens :: (forall as. TEnv as -> Lens (VEnv as) a) -> EnvI LensT a
pattern ULens lens <- EnvI (unLensTdot -> lens)
  where
    ULens lens = EnvI (LT . lens)
{-# COMPLETE ULens #-}

runULens :: EnvI LensT a -> TEnv as -> Lens (VEnv as) a
runULens (ULens lens) = lens


l2v :: [a] -> ((forall n. Vec a n -> r) -> r)
l2v [] k       = k VecNil
l2v (x : xs) k = l2v xs $ \xs' -> k (VecCons x xs')

l2snat :: [a] -> ((forall n. SNat n -> r) -> r)
l2snat [] k       = k SZ
l2snat (_ : xs) k = l2snat xs $ \n -> k (SS n)

v2l :: Vec a n -> [a]
v2l VecNil         = []
v2l (VecCons x xs) = x : v2l xs


runOpenL :: Variables sem =>
  ([EnvI sem a] -> EnvI sem b) -> [proxy] -> ((forall n. SNat n -> sem (Repeat a n) b -> r) -> r)
runOpenL f xs k = l2snat xs $ \sn -> k sn $ UE.runOpenV sn (\as -> f (v2l as))

runAppLens :: ([EnvI LensT a] -> EnvI LensT b) -> Lens [a] b
runAppLens f = L $ \xs ->
  runOpenL f xs $ \sn t -> runLens (lensT2lens t . ll sn) xs
  where
    ll :: SNat n -> Lens [a] (Env Identity (Repeat a n))
    ll sn = L $ \xs -> pure (l2e xs sn , pure . e2l sn)

    l2e :: [a] -> SNat n -> Env Identity (Repeat a n)
    l2e [] SZ           = ENil
    l2e (x : xs) (SS n) = ECons (Identity x) (l2e xs n)
    l2e _ _             = error "l2e: not fixed shape"

    e2l :: SNat n -> Env Identity (Repeat a n) -> [a]
    e2l SZ ENil                        = []
    e2l (SS n) (ECons (Identity a) as) = a : e2l n as

{-
*ELens ELens> let lens = runAppLens (\xs -> foldr consB nilB (reverse xs))
*ELens ELens> get lens [1,2,3]
Right [3,2,1]
*ELens ELens> put lens [1,2,3] [4,5,6]
Right [6,5,4]
-}


runAppLensF :: Traversable t => (t (EnvI LensT a) -> EnvI LensT b) -> Lens (t a) b
runAppLensF f = L $ \t ->
  let xs = Data.Foldable.toList t
      sh = t
  in do
    (y, r) <- runLens (runAppLens (f . fill sh)) xs
    pure (y, r >=> (pure . fill sh))
  where
    fill :: Traversable t => t b -> [a] -> t a
    fill sh xs = State.evalState (traverse (const next) sh) xs
      where
        next = do
          zs <- State.get
          State.put (tail zs)
          return (head zs)

lensT2lens :: LensT as a -> Lens (Env Identity as) a
lensT2lens (LT l0) = l0 . l
  where
    l :: Lens (Env Identity s) (VEnv s)
    l = L $ \xs -> pure (addUsed xs, pure . fromUsed xs)

    addUsed :: Env Identity s -> VEnv s
    addUsed ENil                    = VNil
    addUsed (ECons (Identity x) xs) = VCons (Used x) (addUsed xs)

    fromUsed :: Env Identity s -> VEnv s -> Env Identity s
    fromUsed ENil _ = ENil
    fromUsed (ECons _ xs) (VCons (Used x') xs') = ECons (Identity x') $ fromUsed xs xs'
    fromUsed (ECons x xs) (VCons Unused xs') = ECons x $ fromUsed xs xs'
    fromUsed (ECons x xs) VUndet             = ECons x $ fromUsed xs VUndet

singletonL :: Lens a (Env Identity '[a])
singletonL = L $ \x -> pure (ECons (Identity x) ENil, \(ECons (Identity x') _) -> pure x')

runHOBiT :: (EnvI LensT a1 -> EnvI LensT a2) -> Lens a1 a2
runHOBiT f = lensT2lens (UE.runOpen f) . singletonL

getH :: (EnvI LensT a -> EnvI LensT b) -> a -> Err b
getH = get . runHOBiT

putH :: (EnvI LensT a -> EnvI LensT b) -> a -> b -> Err a
putH = put . runHOBiT

class LiftLens e where
  liftLens :: Lens a b -> e a -> e b

instance LiftLens (EnvI LensT) where
  liftLens lens e = ULens $ \e' -> lens . runULens e e'

class Monoidal i p (e :: k -> Type) | e -> i, e -> p where
  unit :: e i
  pair :: e a -> e b -> e (p a b)

instance Monoidal () (,) (EnvI LensT) where
  unit = UE.liftFO0 (LT unitL)
  pair = UE.liftFO2 splitLT
  -- pair e1 e2 = ULens $ \e -> splitL e (runULens e1 e) (runULens e2 e)

class    (LiftLens e, Monoidal () (,) e) => AppLens e
instance (LiftLens e, Monoidal () (,) e) => AppLens e

constB :: (Eq a, AppLens e) => a -> e a
constB x = liftLens c unit
  where
    c = L $ \_ -> pure (x, \x' -> if x == x' then pure () else throwError "constB: update on a constant")

ununit :: AppLens e => e () -> e r -> e r
ununit e1 e2 = liftLens unUnitL (pair e1 e2)
  where
    unUnitL :: Lens ((), r) r
    unUnitL = L $ \(_, x) -> pure (x, \r -> pure ((), r))

class Monoidal i p e => UnPair i p (e :: k -> Type) | e -> i, i -> p where
  unpair :: e (p a b) -> (e a -> e b -> e r) -> e r

fallback :: a -> Used a -> a
fallback _ (Used x) = x
fallback x Unused   = {- trace "fallback happend" -} x

shareViewLens :: Lens (VEnv s) a -> Lens (VEnv (a ': s)) b -> Lens (VEnv s) b
shareViewLens l1 l2 = L $ \venv -> do
  (x, rx) <- runLens l1 venv
  (y, ry) <- runLens l2 (VCons (Used x) venv)
  let rr y' = do
        vv <- ry y'
        case vv of
          VCons x' venvy' -> do
            venvx' <- rx (fallback x x')
            mergeEnv venvx' venvy'
          VUndet -> rx x
  pure (y, rr)

shareViewLensT :: LensT s a -> LensT (a ': s) b -> LensT s b
shareViewLensT =
  (coerce :: (Lens (VEnv s) a -> Lens (VEnv (a ': s)) b -> Lens (VEnv s) b) -> LensT s a -> LensT (a ': s) b -> LensT s b)
  shareViewLens

unpairLens' :: Lens (VEnv (a ': b ': s)) c -> Lens (VEnv ( (a, b) ': s)) c
unpairLens' l = L $ \case
  VCons (Used (x,y)) venv -> do
      (z, r) <- runLens l $ VCons (Used x) $ VCons (Used y) venv
      let rr z' = do
            vv <- r z'
            case vv of
              VCons x' (VCons y' venv') -> pure $ VCons (Used (fallback x x', fallback y y')) venv'
              VCons x' VUndet           -> pure $ VCons (Used (fallback x x', y)) VUndet
              VUndet                    -> pure $ VCons (Used (x, y)) VUndet
              -- VCons (Used x') (VCons (Used y') venv') -> pure $ VCons (Used (x', y')) venv'
              -- VCons Unused    (VCons Unused venv')    -> pure $ VCons Unused venv'
              -- VCons Unused    VUndet                  -> pure VUndet
              -- VUndet                                  -> pure VUndet
              -- _                                       -> throwError "unpair: introduced variables must be all used or all unused"
      pure (z, rr)
  _ ->
    throwError $ "unpairLens: " ++ msgViolatedMaximalityAssumption

unpairLensT' :: LensT (a ': b ': s) c -> LensT ( (a,b) ': s ) c
unpairLensT' =
  (coerce :: (Lens (VEnv (a ': b ': s)) c -> Lens (VEnv ( (a,b) ': s )) c)
             -> LensT (a ': b ': s) c -> LensT ( (a,b) ': s ) c) unpairLens'

unpairLensT :: LensT s (a, b) -> LensT (a ': b ': s) r -> LensT s r
unpairLensT e1 e2 = shareViewLensT e1 (unpairLensT' e2)
instance UnPair () (,) (EnvI LensT) where
  unpair = UE.liftSOn (LZ :. LS (LS LZ) :. End) unpairLensT

data Sums as where
  InHead :: a       -> Sums (a ': as)
  InTail :: Sums as -> Sums (a ': as)

data LensBranches' s obs rbs r where
  LensBrCons ::
    Lens (VEnv (a ': s)) r -> (r -> Bool) -> (Sums obs -> r -> a)
    -> LensBranches' s obs rbs r
    -> LensBranches' s obs (a ': rbs) r
  LensBrNil ::
    LensBranches' s obs '[] r

type LensBranches s bs = LensBranches' s bs bs

condLens :: String -> LensBranches s bs r -> Lens (VEnv (Sums bs ': s)) r
condLens str branches = L $ \case
  VCons (Used v) venv -> do
    (phi, res, rres) <- h 0 v venv [] id branches
    let back r' | phi r'    = rres r'
                | otherwise = {- trace (str ++ ": trying branch-switching") $ -} branchSwitch 0 v venv id branches r'
    return (res, back)
  _ -> throwError $ str ++ ": " ++ msgViolatedMaximalityAssumption
  where
    h :: Int -> Sums bs -> VEnv s -> [r -> Bool] -> (Sums bs -> Sums obs) -> LensBranches' s obs bs r -> Err (r -> Bool, r, r -> Err (VEnv (Sums obs ': s)))
    h n (InHead a) venv _ps inj (LensBrCons l phi _recon _brs) = do
        (res, rres) <- runLens l (VCons (Used a) venv)
        unless ({- all (\p -> not (p res)) ps && -} phi res) $ throwError $ str ++ ": runtime checking failed (fwd)"
        let rres' res' = do
              vv <- rres res'
              case vv of
                VCons (Used a') venv' -> pure $ VCons (Used $ inj $ InHead a') venv'
                _                     -> throwError $ str ++ ": unresolved value (bwd; branch #" ++ show (n + 1) ++ ")"
                -- VCons Unused venv'    -> pure $ VCons Unused venv'
                -- VUndet                -> pure VUndet
        pure (phi, res, rres')
    h n (InTail xs) venv ps inj (LensBrCons _ phi _ brs) = h (n + 1) xs venv (phi : ps) (inj . InTail) brs

    branchSwitch :: Int -> Sums obs -> VEnv s -> (Sums bs -> Sums obs) -> LensBranches' s obs bs r -> r -> Err (VEnv (Sums obs ': s))
    branchSwitch n v venv inj (LensBrCons l phi recon brs) r
      | phi r = do
        (_, rres) <- runLens l (VCons (Used $ recon v r) venv)
        vv <- rres r
        case vv of
          VCons (Used x') venv' -> pure $ VCons (Used $ inj $ InHead x') venv'
          _                     -> throwError $ str ++ ": unresolved value (bwd; branch-switch; branch #" ++ show (n + 1) ++ ")"
          -- VCons Unused    venv' -> pure $ VCons Unused venv'
          -- VUndet                -> pure VUndet
      | otherwise = branchSwitch (n + 1) v venv (inj . InTail) brs r
    branchSwitch _ _ _ _ LensBrNil _ =
      throwError "match failure (bwd)"
{-

To apply, liftSO, we need to convert it term rep form.

condLensTermRep :: WithRecon bs r -> Env (TermRep LensT s) ([] :~> Sums bs ': BrSig bs r) -> LensT s r

-}

type family BrSig bs r = s | s -> bs where
  BrSig '[] r = '[]
  BrSig (b ': bs) r = ('[b] ':~> r) ': BrSig bs r


type WithRecon bs r = WithRecon' bs bs r
data WithRecon' obs rbs r where
  WRNil  :: WithRecon' obs '[] r
  WRCons ::  (r -> Bool) -> (Sums obs -> r -> a) -> WithRecon' obs rbs r -> WithRecon' obs (a ': rbs) r

condLensTermRep :: String -> WithRecon bs r -> Env (TermRep LensT s) ('[] ':~> Sums bs ': BrSig bs r) -> LensT s r
condLensTermRep str brs (ECons (TR e) branches) = shareViewLensT e (LT $ condLens str $ conv brs branches)
  where
    conv :: WithRecon' obs rbs r -> Env (TermRep LensT s) (BrSig rbs r) ->  LensBranches' s obs rbs r
    conv WRNil _ = LensBrNil
    conv (WRCons with recon wrs) (ECons (TR lt) es) = LensBrCons (unLensT lt) with recon (conv wrs es)

data BranchExps' e oas as r where
  BrExCons ::
    (e a -> e r) -> (r -> Bool) -> (Sums oas -> r -> a)
    -> BranchExps' e oas as r
    -> BranchExps' e oas (a ': as) r

  BrExNil ::
    BranchExps' e oas '[] r

type BranchExps e as r = BranchExps' e as as r

class WithBxCase e where
  branch :: String -> e (Sums as) -> BranchExps e as r -> e r

class    (UnPair () (,) e, WithBxCase e, AppLens e) => HOBiT e
instance (UnPair () (,) e, WithBxCase e, AppLens e) => HOBiT e

mkURepArg :: EnvI LensT (Sums bs) -> BranchExps (EnvI LensT) bs r -> (WithRecon bs r, Env (URep LensT) ('[] ':~> Sums bs ': BrSig bs r))
mkURepArg e0 branches =
   let (wrs, es) = conv branches
  in (wrs, ECons (UR ENil (const e0)) es)
  where
    conv :: BranchExps' (EnvI LensT) obs rbs r -> (WithRecon' obs rbs r, Env (URep LensT) (BrSig rbs r))
    conv BrExNil = (WRNil, ENil)
    conv (BrExCons k with recon brs)  =
      let (wrs, es) = conv brs
      in (WRCons with recon wrs, ECons (UR (ECons Proxy ENil) (\(ECons a _) -> k a)) es)

instance WithBxCase (EnvI LensT) where
  branch str e branches =
    let (wrs, es) = mkURepArg e branches
    in UE.liftSO (condLensTermRep str wrs) es

-- For extensibility, we will use shallow embedding for patterns
-- We can view patterns as linear-typed open terms (with no binders),
-- and use difference lists to reprensents terms as Polakow.

data PatBuilder i o a =
  PatBuilder
  (TEnv i -> TEnv o)
  (a -> Env Identity i -> Err (Env Identity o))
  (Env Identity o -> Err (a, Env Identity i))

data Pat as a = Pat (TEnv as) (PInj a (Env Identity as))

pat :: PatBuilder '[] o a -> Pat o a
pat (PatBuilder s p c) = Pat (s ENil) (PInj f finv)
  where
    f x  = p x ENil
    finv = fmap fst . c

constP :: Eq a => a -> PatBuilder i i a
constP a =
  PatBuilder id (\a' s -> if a == a' then pure s else throwError "constP: match failure")
                (\s -> pure (a, s))


varP :: PatBuilder i (a ': i) a
varP = PatBuilder
       (ECons Proxy)
       (\x s -> pure (ECons (Identity x) s))
       (\(ECons (Identity x) s) -> pure (x, s))

unitP :: PatBuilder i i ()
unitP = PatBuilder id (\_ s -> pure s) (\s -> pure ((), s))

pairP :: PatBuilder m o a -> PatBuilder i m b -> PatBuilder i o (a, b)
pairP (PatBuilder s1 p1 c1) (PatBuilder s2 p2 c2) = PatBuilder s p c
  where
    s = s1 . s2
    p (x, y) env =
      p1 x =<< p2 y env
    c env = do
      (x, env')  <- c1 env
      (y, env'') <- c2 env'
      return ((x,y), env'')

data PInj a b = PInj (a -> Err b) (b -> Err a)

pinjP :: PInj a b -> PatBuilder i o b -> PatBuilder i o a
pinjP (PInj f finv) (PatBuilder s p c) = PatBuilder s p' c'
  where
    p' x env = do
      y <- f x
      p y env
    c' env = do
      (y, env') <- c env
      x <- finv y
      return (x, env')

data Branch e a r =
  forall as. Branch (Pat as a) (Env e as -> e r) (r -> Bool) (a -> r -> a)

(-->) :: PatBuilder '[] as a -> (Func e as (e r), r -> Bool, a -> r -> a) -> Branch e a r
p --> (f, phi, recon) =
  let p'@(Pat _ _) = pat p
  in Branch p' (fromFunc f) phi recon

(-->!) :: PatBuilder '[] as a -> Func e as (e r) -> Branch e a r
p -->! f = p --> (f, const True, const)

infixl 0 -->
infixl 0 -->!


data IBranchExps e a0 as r where
  IBrExCons ::
    (e a -> e r) -> (r -> Bool) -> (a0 -> r -> a)
    -> IBranchExps e a0 as r
    -> IBranchExps e a0 (a ': as) r

  IBrExNil ::
    IBranchExps e a0 '[] r


case_ ::
  (UnPair () (,) e, WithBxCase e, AppLens e)
  => String -> e a -> [Branch e a r] -> e r
case_ str e brs = convertBranch brs $ \p bs' ->
  branch str (liftLens (fromPInj p) e) $ convBr p bs'
  where
    convBr :: PInj a (Sums as0) -> IBranchExps e a as r -> BranchExps' e as0 as r
    convBr _ IBrExNil                                    = BrExNil
    convBr p@(PInj _ finv) (IBrExCons body phi recon bs) = BrExCons body phi (\x -> recon (fromRight (error "reconciliation: Left") $ finv x)) (convBr p bs)

fromPInj :: PInj x y -> Lens x y
fromPInj (PInj f finv) = L $ \x ->
  case f x of
    Left s -> throwError $ "fromPInj: partial (fwd) [" ++ s ++ "]"
    Right y  ->
      let rr y' = case finv y' of
            Left s   -> throwError $ "fromPInj: partial (bwd) [" ++ s ++ "]"
            Right x' -> pure x'
      in pure (y, rr)

liftPInj :: LiftLens e => PInj a b -> e a -> e b
liftPInj pinj = liftLens (fromPInj pinj)


convertBranch ::
  (UnPair () (,) e, AppLens e) => [Branch e a r] -> (forall as. PInj a (Sums as) -> IBranchExps e a as r -> res) -> res
convertBranch [] k = k abort IBrExNil
  where
    abort = PInj (const $ throwError "abort") (const $ throwError "abort")
--    abortL = Lens $ const $ throwError "aborted"
convertBranch (Branch (Pat sh_as (PInj f finv)) body phi recon : bs) k =
  convertBranch bs $ \(PInj g ginv) bs' ->
                       let p = PInj (\x -> case f x of
                                             Left _  -> InTail <$> g x
                                             Right y -> pure $ InHead y)
                                    (\case
                                        InHead z -> finv z
                                        InTail z -> do
                                          res <- ginv z
                                          case f res of
                                            Left _  -> pure res
                                            Right _ -> throwError "pattern: preceding patterns must not match with the backward computation result.")
                           recon' s v = fromRight (error "reconciliation failed") $ f (recon s v)
                       in  k p (IBrExCons (convBody sh_as body) phi recon'  bs')

convBody :: (UnPair () (,) e, AppLens e) => TEnv as -> (Env e as -> e r) -> e (Env Identity as) -> e r
convBody ENil f e         = ununit (liftLens u2nL e) (f ENil)
  where
    u2nL :: Lens (Env Identity '[]) ()
    u2nL = L $ const $ pure ((), const (pure ENil))
convBody (ECons _ sh) f e = unpair (liftLens c2pL e) $ \a e' -> convBody sh (f . ECons a) e'
  where
    c2pL :: Lens (Env Identity (a ': as)) (a, Env Identity as)
    c2pL = L $ \(ECons (Identity a) as) -> pure ((a, as), \(a', as') -> pure $ ECons (Identity a') as')

nilPInj :: PInj [a] ()
nilPInj = PInj (\case { [] -> pure (); _ -> throwError "non-nil" }) (const $ pure [])

consPInj :: PInj [a] (a,[a])
consPInj = PInj (\case { a:as -> pure (a, as); _ -> throwError "non-cons" }) (\(a,as) -> pure (a : as))

invert :: PInj a b -> PInj b a
invert (PInj f finv) = PInj finv f

leftP :: PatBuilder i o b1 -> PatBuilder i o (Either b1 b2)
leftP = pinjP leftPInj
  where
    leftPInj = PInj (\case { Left a -> pure a; Right _ -> throwError "non-left"}) (pure . Left)

rightP :: PatBuilder i o b -> PatBuilder i o (Either a b)
rightP = pinjP rightPInj
  where
    rightPInj = PInj (\case { Right a -> pure a; Left _ -> throwError "non-right"}) (pure . Right)

nilP :: PatBuilder o o [a]
nilP = pinjP nilPInj unitP

consP :: PatBuilder m o a -> PatBuilder i m [a] -> PatBuilder i o [a]
consP p1 p2 = pinjP consPInj $ pairP p1 p2

nilB :: (LiftLens e, Monoidal () (,) e) => e [a]
nilB = liftPInj (invert nilPInj) unit

consB :: (LiftLens e, Monoidal () (,) e) => e a -> e [a] -> e [a]
consB x y = liftPInj (invert consPInj) $ pair x y

unlist ::
  (UnPair () (,) e, WithBxCase e, LiftLens e) =>
  e [a]
  -> e r -> (r -> Bool) -> ([a] -> r -> [a])
  -> (e a -> e [a] -> e r) -> (r -> Bool) -> ([a] -> r -> [a])
  -> e r
unlist e n phin reconn c phic reconc =
  case_ "unlist" e
  [ Branch (pat nilP) (const n) phin reconn,
    Branch (pat $ consP varP varP) (\(ECons x (ECons y _)) -> c x y) phic reconc ]


linesB :: HOBiT e => e String -> e [String]
linesB str =
  unpair (breakNLB str) $ \f b ->
  case_ "linesB-case" b
  [ consP (constP '\n') (consP varP  varP) -->
    (\x r -> f `consB` linesB (x `consB` r),
    (> 1) .length,
    \_b _ -> '\n' : ' ' : _b),
    varP
    --> (\_ -> consB f nilB,
         (== 1) . length,
         \_b _ -> lastNL _b) ]
    -- [ Branch (pat $ consP (constP '\n') $ consP varP varP)
    --        (\(ECons x (ECons r _)) -> consB f (linesB (consB x r)))
    --        ((> 1) . length)
    --        (\_b _ -> '\n' : ' ' : _b),
    -- Branch (pat varP) (\_ -> consB f nilB)
    --        ((== 1) . length)
    --        (\_b _ -> lastNL _b) ]
  where
    lastNL []      = []
    lastNL ['\n']  = ['\n']
    lastNL (_ : x) = lastNL x

breakNLB :: HOBiT e => e String -> e (String, String)
breakNLB str = case_ "breakNLB-case" str
  [ nilP -->
    (pair nilB nilB, p1, const $ const []),
    consP (constP '\n') varP -->
    (\s -> pair nilB (constB '\n' `consB` s), p2, \_ _ -> "\n"),
    consP varP varP -->
    (\c s ->
        unpair (breakNLB s) $ \f r ->
        pair (consB c f) r,
      p3, \_ _ -> " ") ]
  where
    p1 (x, y) = null x && null y
    p2 (x, y) = null x && not (null y)
    p3 (x, _) = not (null x)

linesL :: Lens String [String]
linesL = runHOBiT linesB

-- >>> get linesL "AA\nBB"
-- Right ["AA","BB"]
-- >>> put linesL  "AA\nBB" ["a", "b"]
-- Left "breakNLB-case: unresolved value (bwd; branch-switch; branch #1)"
-- >>> put linesL "AA\nBB" ["a", "b", "c"]
-- Left "breakNLB-case: unresolved value (bwd; branch #1)"
-- >>> put linesL "AA\nBB" ["a"]
-- Left "breakNLB-case: unresolved value (bwd; branch-switch; branch #1)"

-- >>> get linesL "AA\nBB\n"
-- Right ["AA","BB"]
-- >>> put linesL "AA\nBB\n" ["a", "b"]
-- Right "a\nb\n"
-- >>> put linesL "AA\nBB\n" ["a", "b", "c"]
-- Right "a\nb\nc\n"
-- >>> put linesL "AA\nBB\n" ["a"]
-- Right "a\n"
