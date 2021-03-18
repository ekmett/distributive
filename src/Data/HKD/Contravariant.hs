{-# Language GeneralizedNewtypeDeriving #-}
{-# Language Trustworthy #-}

-- |
-- Copyright :  (c) 2019-2021 Edward Kmett
--              (c) 2019 Oleg Grenrus
--              (c) 2017-2021 Aaron Vargo 
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Oleg Grenrus <oleg.grenrus@iki.fi>
-- Stability :  experimental
-- Portability: non-portable
--
-- "Higher-Kinded Data" such as it is
--
-- Simple usage:
--
-- @
-- data Record f = Record
--   { fieldInt    :: f Int
--   , fieldString :: f String
--   , fieldSome   :: 'Some' f
--   } deriving ('Generic1', 'FFunctor', 'FFoldable', 'FTraversable')
-- @
--
-- Generically derived 'FZip' and 'FRepeat':
--
-- @
-- data Record f = Record
--   { fieldInt    :: f Int
--   , fieldString :: f String
--   } deriving ('Generic1', 'FZip', 'FRepeat')
-- @
module Data.HKD.Contravariant
( FContravariant(..)
, FEquivalence(..)
, FComparison(..)
, FOp(..)
) where

import Control.Applicative
import Control.Applicative.Backwards
import Data.Coerce (coerce)
import Data.Distributive.Internal.Coerce
import Data.Functor.Compose (Compose (..))
import Data.Functor.Product (Product (..))
import Data.Functor.Reverse
import Data.Functor.Sum (Sum (..))
import Data.GADT.Compare
import Data.HKD
import Data.Kind (Type)
import qualified Data.Monoid as Monoid
import Data.Proxy (Proxy (..))
import Data.Type.Equality
import GHC.Generics

-------------------------------------------------------------------------------
-- FContravariant
-------------------------------------------------------------------------------

class FContravariant (t :: (k -> Type) -> Type) where
  fcontramap :: (f ~> g) -> t g -> t f
  default fcontramap :: (Generic1 t, FContravariant (Rep1 t)) => (f ~> g) -> t g -> t f
  fcontramap f = to1 . fcontramap f . from1
  {-# inline fcontramap #-}

instance FContravariant Proxy where
  fcontramap _ Proxy = Proxy
  {-# inline fcontramap #-}

instance FContravariant (Const a) where
  fcontramap _ (Const a) = Const a
  {-# inline fcontramap #-}

instance (Functor f, FContravariant g) => FContravariant (Compose f g) where
  fcontramap f = Compose #. fmap (fcontramap f) .# getCompose
  {-# inline fcontramap #-}

instance (FContravariant f, FContravariant g) => FContravariant (Product f g) where
  fcontramap f (Pair g h) = Pair (fcontramap f g) (fcontramap f h)
  {-# inline fcontramap #-}

instance (FContravariant f, FContravariant g) => FContravariant (Sum f g) where
  fcontramap f (InL g) = InL (fcontramap f g)
  fcontramap f (InR h) = InR (fcontramap f h)
  {-# inline fcontramap #-}

instance FContravariant (K1 i a) where
  fcontramap _ = coerce
  {-# inline fcontramap #-}

deriving newtype instance FContravariant f => FContravariant (M1 i c f)
deriving newtype instance FContravariant f => FContravariant (Rec1 f)

instance FContravariant U1 where
  fcontramap _ U1 = U1
  {-# inline fcontramap #-}

instance FContravariant V1 where
  fcontramap _ = \case
  {-# inline fcontramap #-}

instance (Functor f, FContravariant g) => FContravariant (f :.: g) where
  fcontramap f = Comp1 #. fmap (fcontramap f) .# unComp1
  {-# inline fcontramap #-}

instance (FContravariant f, FContravariant g) => FContravariant (f :*: g) where
  fcontramap f (g :*: h) = fcontramap f g :*: fcontramap f h
  {-# inline fcontramap #-}

instance (FContravariant f, FContravariant g) => FContravariant (f :+: g) where
  fcontramap f (L1 g) = L1 (fcontramap f g)
  fcontramap f (R1 h) = R1 (fcontramap f h)
  {-# inline fcontramap #-}

deriving newtype instance FContravariant f => FContravariant (Backwards f)
deriving newtype instance FContravariant f => FContravariant (Reverse f)
deriving newtype instance FContravariant f => FContravariant (Monoid.Alt f)
deriving newtype instance FContravariant f => FContravariant (Monoid.Ap f)
deriving anyclass instance FContravariant F0 

newtype FEquivalence a = FEquivalence
  { getFEquivalence :: forall x y. a x -> a y -> Maybe (x :~: y)
  }

instance FContravariant FEquivalence where
  fcontramap f (FEquivalence g) = FEquivalence \i j -> g (f i) (f j)
  {-# inline fcontramap #-}

newtype FComparison a = FComparison
  { getFComparison :: forall x y. a x -> a y -> GOrdering x y
  }

instance FContravariant FComparison where
  fcontramap f (FComparison g) = FComparison \i j -> g (f i) (f j)
  {-# inline fcontramap #-}

newtype FOp b f = FOp { getFOp :: forall x. f x -> b }

instance FContravariant (FOp b) where
  fcontramap f (FOp g) = FOp (g . f)
  {-# inline fcontramap #-}

