{-

[New] Polymorphism example. More specifically, this module unembeds a language
that contains a type (Forall f) that is isomorphic to Haskell-level polymorphic
expression.

  gen : ( forall f. e (f a) ) ~ e (Forall f) : inst

Known Issue: Currently, we need to know internal details of EbU to unembed a
construct corresponds to the left-to-right conversion.

2024-11-13 Kazutaka Matsuda

-}

{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE DerivingStrategies        #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE PolyKinds                 #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeOperators             #-}

{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use section" #-}
{-# LANGUAGE InstanceSigs              #-}

module Unembedding.Examples.Forall where
import           Data.Kind       (Type)
import           Data.Proxy      (Proxy (Proxy))
import qualified Unembedding     as UE
import           Unembedding     (Dim (..), LiftVariables (..), Variables, ol0,
                                  ol1)
import qualified Unembedding.Env as UE

import           DeFun.Core      (App, type (@@), type (~>))


data T = O | T :~> T | Forall (T ~> T)

infixr 0 :~>

class L (e :: T -> Type) where
  lam :: (e a -> e b) -> e (a :~> b)
  app :: e (a :~> b) -> e a -> e b
  let_ :: e a -> (e a -> e b) -> e b

  -- used Proxy to avoid "ambiguous type variable" errors (@@) is non-injective
  gen  :: (forall a. Proxy a -> e (f @@ a)) -> e (Forall f)
  inst :: e (Forall f) -> Proxy a -> e (f @@ a)

combK :: L e => e (a :~> b :~> a)
combK = lam $ \a -> lam $ const a

-- We should prepare template haskell to generate the following code.
data KType as :: T ~> T
data IdType :: T ~> T

type instance App (KType '[]) a = Forall (KType '[a])
type instance App (KType '[a]) b = a :~> b :~> a
type instance App IdType a = a :~> a

combKgen :: L e => e (Forall (KType '[]))
combKgen = gen $ const $ gen $ const combK

ex :: L e => e (b :~> b)
ex =
  let_ combKgen (\k ->
    inst (inst k Proxy) Proxy `app` lam id `app` (inst (inst k Proxy) Proxy `app` combK `app` combK))

withFType :: e (Forall f) -> proxy f -> e (Forall f)
withFType e _ = e

ex2 :: L e => e (a :~> a)
ex2 =
  let_ (gen (const $ lam id) `withFType` (Proxy @IdType)) $ \k -> inst k Proxy `app` inst k Proxy

data Ast (env :: [T]) (a :: T) where
  Var :: UE.Ix env a -> Ast env a
  Lam :: Ast (a : env) b -> Ast env (a :~> b)
  App :: Ast env (a :~> b) -> Ast env a -> Ast env b
  Let :: Ast env a -> Ast (a : env) b -> Ast env b

  Gen :: (forall a. Proxy a -> Ast env (App f a)) -> Ast env (Forall f)
  Inst :: Ast env (Forall f) -> Proxy a -> Ast env (App f a)

instance Show (Ast env a) where
  showsPrec k (Var a) = showParen (k > 9) $ showString "Var " . showsPrec 10 a
  showsPrec k (Lam e) = showParen (k > 9) $ showString "Lam " . showsPrec 10 e
  showsPrec k (App e1 e2) = showParen (k > 9) $ showString "App " . showsPrec 10 e1 . showString " " . showsPrec 10 e2
  showsPrec k (Let e1 e2) = showParen (k > 9) $ showString "Let " . showsPrec 10 e1 . showString " " . showsPrec 10 e2
  showsPrec k (Gen e) = showParen (k > 9) $ showString "Gen " . showsPrec 10 (e Proxy)
  showsPrec k (Inst e _) = showParen (k > 9) $ showString "Inst " . showsPrec 10 e


instance LiftVariables Ast where
  type Var Ast = UE.Ix
  liftVar = Var

data P (f :: T ~> T) (r :: T) where
  MkP :: forall f a. Proxy a -> P f (f @@ a)
instance L (UE.EnvI Ast) where
  lam = UE.liftSOn (ol1 :. End) Lam

  app = UE.liftFO2 App
  let_ = UE.liftSOn (ol0 :. ol1 :. End) Let

  inst a p = UE.liftFO1 (flip Inst p) a

  -- Little awkward
  gen :: forall f. (forall (a :: T). Proxy a -> UE.EnvI Ast (f @@ a)) -> UE.EnvI Ast (Forall f)
  gen e = UE.liftFOF (\arg -> Gen (arg . MkP @f)) (\(MkP p) -> e p)


toAst :: (forall e. L e => e a) -> Ast '[] a
toAst = UE.runClose

data S a where
  SO :: Int -> S O
  SF :: (S a -> S b) -> S (a :~> b)
  SG :: (forall a. Proxy a -> S (App f a)) -> S (Forall f)


newtype Sem env a = Sem { interp :: UE.Env S env -> S a }

lamSem :: Sem (a : env) b -> Sem env (a :~> b)
lamSem e = Sem $ \env -> SF $ \a -> interp e (UE.ECons a env)

appSem :: Sem env (a :~> b) -> Sem env a -> Sem env b
appSem e1 e2 = Sem $ \env ->
  case interp e1 env of
    SF h -> h (interp e2 env)

letSem :: Sem env a -> Sem (a : env) b -> Sem env b
letSem e1 e2 = Sem $ \env -> interp e2 (UE.ECons (interp e1 env) env)

genSem :: (forall a. Proxy a -> Sem env (App f a)) -> Sem env (Forall f)
genSem h = Sem $ \env -> SG $ \p -> interp (h p) env

instSem :: Sem env (Forall f) -> Proxy a -> Sem env (App f a)
instSem e p = Sem $ \env ->
  case interp e env of
    SG h -> h p

instance Variables Sem where
  var = Sem $ \(UE.ECons x _) -> x

  weaken e = Sem $ \(UE.ECons _ xs) -> interp e xs

instance LiftVariables Sem

instance L (UE.EnvI Sem) where
 lam = UE.liftSOn (ol1 :. End) lamSem

 app = UE.liftFO2 appSem
 let_ = UE.liftSOn (ol0 :. ol1 :. End) letSem

 inst a p = UE.liftFO1 (flip instSem p) a

  -- Little awkward
 gen :: forall f. (forall (a :: T). Proxy a -> UE.EnvI Sem (f @@ a)) -> UE.EnvI Sem (Forall f)
 gen e = UE.liftFOF (\arg -> genSem (arg . MkP @f)) (\(MkP p) -> e p)

interpL :: (forall e. L e => e a) -> S a
interpL e  = interp (UE.runClose e) UE.ENil

-- >>> toAst combK
-- Lam (Lam (Var IxS IxZ))
-- >>> toAst ex
-- Let (Gen (Gen (Lam (Lam (Var IxS IxZ))))) (App (App (Inst (Inst (Var IxZ))) (Lam (Var IxZ))) (App (App (Inst (Inst (Var IxZ))) (Lam (Lam (Var IxS IxZ)))) (Lam (Lam (Var IxS IxZ)))))
-- >>> toAst ex2
-- Let (Gen (Lam (Var IxZ))) (App (Inst (Var IxZ)) (Inst (Var IxZ)))

-- >>> let SF h = interpL ex in let SO r = h (SO 42) in r
-- 42

-- >>> let SF h = interpL ex2 in let SO r = h (SO 42) in r
-- 42
