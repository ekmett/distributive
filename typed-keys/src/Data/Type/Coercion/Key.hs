{-# language AllowAmbiguousTypes #-}
{-# language TypeOperators #-}
{-# language TypeFamilies #-}
{-# language FlexibleContexts #-}
{-# language QuantifiedConstraints #-}
{-# language ConstraintKinds #-}
{-# language UndecidableInstances #-}
{-# language PolyKinds #-}
{-# language ScopedTypeVariables #-}
{-# language RankNTypes #-}
{-# language GADTs #-}
{-# language RoleAnnotations #-}
{-# language MultiParamTypeClasses #-}

-- |
-- Copyright :  (c) Edward Kmett 2018-2020
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable
--
-- This construction is based on
-- <https://people.seas.harvard.edu/~pbuiras/publications/KeyMonadHaskell2016.pdf The Key Monad: Type-Safe Unconstrained Dynamic Typing>
-- by Atze van der Ploeg, Koen Claessen, and Pablo Buiras

module Data.Type.Coercion.Key
  ( Key, newKey, KeyM
  , Box(Box), unlock, BoxM
  , Representational
  ) where

import Control.Monad.Primitive
import Data.Coerce
import Data.HKD
import Data.Kind
import Data.Primitive.MutVar
import Data.Proxy
import Data.Type.Coercion
import Unsafe.Coerce

type role Key nominal representational
newtype Key s a = Key (MutVar s (Proxy a))
  deriving Eq

type KeyM m = Key (PrimState m)

instance TestCoercion (Key s) where
  testCoercion (Key s :: Key s a) (Key t)
    | s == unsafeCoerce t = Just $ unsafeCoerce (Coercion :: Coercion a a)
    | otherwise           = Nothing
  {-# inline testCoercion #-}

newKey :: PrimMonad m => m (KeyM m a)
newKey = Key <$> newMutVar Proxy
{-# inline newKey #-}

type role Box nominal representational
data Box s f where
  Box :: {-# unpack #-} !(Key s a) -> f a -> Box s f

type BoxM m = Box (PrimState m)

type Representational f =
  (forall a b. Coercible a b => Coercible (f a) (f b)) :: Constraint

unlock :: Representational f => Key s a -> Box s f -> Maybe (f a)
unlock k (Box l x) = case testCoercion k l of
  Just Coercion -> Just (coerce x)
  Nothing -> Nothing
{-# inline unlock #-}

instance
  ( forall a. Eq (f a)
  , Representational f
  ) => Eq (Box s f) where
  Box k v == Box k' v' = case testCoercion k k' of
    Just Coercion -> v == coerce v'
    Nothing -> False
  {-# inline (==) #-}

instance FFunctor (Box s) where
  ffmap f (Box k g) = Box k (f g)
  {-# inline ffmap #-}

instance FFoldable (Box s) where
  ffoldMap f (Box _ g) = f g
  flengthAcc n _ = n + 1
  {-# inline ffoldMap #-}
  {-# inline flengthAcc #-}

instance FTraversable (Box s) where
  ftraverse f (Box k g) = Box k <$> f g
  {-# inline ftraverse #-}

instance FFunctorWithIndex (Key s) (Box s) where
  ifmap f (Box k g) = Box k (f k g)
  {-# inline ifmap #-}

instance FFoldableWithIndex (Key s) (Box s) where
  iffoldMap f (Box k g) = f k g
  {-# inline iffoldMap #-}

instance FTraversableWithIndex (Key s) (Box s) where
  iftraverse f (Box k g) = Box k <$> f k g
  {-# inline iftraverse #-}
