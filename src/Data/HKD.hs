{-# language BlockArguments #-}
{-# language FlexibleContexts #-}
{-# language FlexibleInstances #-}
{-# language DefaultSignatures #-}
{-# language DeriveTraversable #-}
{-# language DeriveAnyClass #-}
{-# language DeriveGeneric #-}
{-# language ConstraintKinds #-}
{-# language GADTs #-}
{-# language MultiParamTypeClasses #-}
{-# language PolyKinds #-}
{-# language StandaloneDeriving #-}
{-# language RoleAnnotations #-}
{-# language DerivingStrategies #-}
{-# Language GeneralizedNewtypeDeriving #-}
{-# Language QuantifiedConstraints #-}
{-# language RankNTypes #-}
{-# language ScopedTypeVariables #-}
{-# language Trustworthy #-}
{-# language TypeFamilies #-}
{-# language TypeOperators #-}
{-# language LambdaCase #-}
{-# language EmptyCase #-}

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
module Data.HKD
(
-- * "Natural" transformation
   type (~>)
-- * Functor
, FFunctor(..)
, gffmap
-- * Foldable
, FFoldable(..)
, gffoldMap
, flength
, ftraverse_
, ffor_
-- * Traversable
, FTraversable(..)
, ffmapDefault
, ffoldMapDefault
, ffor
, fsequence
-- * Zip & Repeat
, FZip(..)
, FRepeat(..)
-- * Higher kinded data
-- | See also "Data.Some" in @some@ package. This package provides instances for it.
, F0(..)
, F1(..)
, F2(..)
, F3(..)
, F4(..)
, F5(..)
, FConstrained(..)
, FCompose(..)
, NT(..)
, Limit(..)
, Dict1(..)
) where

import Control.Applicative
import Control.Applicative.Backwards
import Data.Proxy (Proxy (..))
import Data.Coerce (coerce)
import Data.Functor.Constant
import Data.Functor.Compose (Compose (..))
import Data.Functor.Confusing
import Data.Functor.Identity (Identity (..))
import Data.Functor.Product (Product (..))
import Data.Functor.Reverse
import Data.Functor.Sum (Sum (..))
import qualified Data.Monoid as Monoid
import Data.Kind (Type)
import Data.Semigroup (Semigroup (..))
import qualified Data.Some.GADT as G
import Data.Some.Newtype (Some (..), mapSome, foldSome, withSome)
import qualified Data.Some.Church as C
import Data.Distributive.Internal.Coerce
import GHC.Generics
import Unsafe.Coerce

-------------------------------------------------------------------------------
-- wiggly arrow
-------------------------------------------------------------------------------

type f ~> g = forall a. f a -> g a
infixr 0 ~>

-------------------------------------------------------------------------------
-- FFunctor
-------------------------------------------------------------------------------

class FFunctor (t :: (k -> Type) -> Type) where
  ffmap :: (f ~> g) -> t f -> t g
  default ffmap :: FTraversable t => (f ~> g) -> t f -> t g
  ffmap = ffmapDefault
  {-# inline ffmap #-}

gffmap :: (Generic1 t, FFunctor (Rep1 t)) => (f ~> g) -> t f -> t g
gffmap f = to1 . ffmap f . from1
{-# inline gffmap #-}

instance FFunctor Proxy where
  ffmap = \_ -> coerce
  {-# inline ffmap #-}

instance FFunctor (Const a) where
  ffmap = \_ -> coerce
  {-# inline ffmap #-}

instance FFunctor (Constant a) where
  ffmap = \_ -> coerce
  {-# inline ffmap #-}

instance (Functor f, FFunctor g) => FFunctor (Compose f g) where
  ffmap f = Compose #. fmap (ffmap f) .# getCompose
  {-# inline ffmap #-}

instance (FFunctor f, FFunctor g) => FFunctor (Product f g) where
  ffmap f (Pair g h) = Pair (ffmap f g) (ffmap f h)
  {-# inline ffmap #-}

instance (FFunctor f, FFunctor g) => FFunctor (Sum f g) where
  ffmap f (InL g) = InL (ffmap f g)
  ffmap f (InR h) = InR (ffmap f h)
  {-# inline ffmap #-}

instance FFunctor (K1 i a) where
  ffmap _ = coerce
  {-# inline ffmap #-}

deriving newtype instance FFunctor f => FFunctor (M1 i c f)
deriving newtype instance FFunctor f => FFunctor (Rec1 f)

instance FFunctor U1
instance FFunctor V1

instance (Functor f, FFunctor g) => FFunctor (f :.: g) where
  ffmap f = Comp1 #. fmap (ffmap f) .# unComp1
  {-# inline ffmap #-}

instance (FFunctor f, FFunctor g) => FFunctor (f :*: g) where
  ffmap f (g :*: h) = ffmap f g :*: ffmap f h
  {-# inline ffmap #-}

instance (FFunctor f, FFunctor g) => FFunctor (f :+: g) where
  ffmap f (L1 g) = L1 (ffmap f g)
  ffmap f (R1 h) = R1 (ffmap f h)
  {-# inline ffmap #-}

-------------------------------------------------------------------------------
-- FFoldable
-------------------------------------------------------------------------------

class FFoldable (t :: (k -> Type) -> Type) where
  ffoldMap :: Monoid m => (forall a. f a -> m) -> t f -> m
  default ffoldMap :: (FTraversable t, Monoid m) => (forall a. f a -> m) -> t f -> m
  ffoldMap = ffoldMapDefault
  {-# inline ffoldMap #-}

  flengthAcc :: Int -> t f -> Int
  flengthAcc acc t = acc + Monoid.getSum (ffoldMap (\_ -> Monoid.Sum 1) t)
  {-# inline flengthAcc #-}

gffoldMap :: (Generic1 t, FFoldable (Rep1 t), Monoid m) => (forall a. f a -> m) -> t f -> m
gffoldMap f = ffoldMap f . from1
{-# inline gffoldMap #-}

flength :: FFoldable t => t f -> Int
flength = flengthAcc 0
{-# inline flength #-}

ftraverse_ :: (FFoldable t, Applicative m) => (forall a. f a -> m b) -> t f -> m ()
ftraverse_ k tf = withSome (ffoldMap (Some . k) tf) (() <$)
{-# inline ftraverse_ #-}

ffor_ :: (FFoldable t, Applicative m) => t f -> (forall a. f a -> m b) -> m ()
ffor_ tf k = ftraverse_ k tf
{-# inline ffor_ #-}

instance FFoldable Proxy where
  flengthAcc = const
  {-# inline flengthAcc #-}

instance FFoldable (Const a) where
  flengthAcc = const
  {-# inline flengthAcc #-}

instance FFoldable (Constant a) where
  flengthAcc = const
  {-# inline flengthAcc #-}

instance (Foldable f, FFoldable g) => FFoldable (Compose f g) where
  ffoldMap f = foldMap (ffoldMap f) .# getCompose
  {-# inline ffoldMap #-}

instance (FFoldable f, FFoldable g) => FFoldable (Product f g) where
  ffoldMap f (Pair g h) = ffoldMap f g `mappend` ffoldMap f h
  flengthAcc f (Pair g h) = f `flengthAcc` g `flengthAcc` h
  {-# inline ffoldMap #-}
  {-# inline flengthAcc #-}

instance (FFoldable f, FFoldable g) => FFoldable (Sum f g) where
  ffoldMap f (InL g) = ffoldMap f g
  ffoldMap f (InR h) = ffoldMap f h
  flengthAcc f (InL g) = flengthAcc f g
  flengthAcc f (InR h) = flengthAcc f h
  {-# inline ffoldMap #-}
  {-# inline flengthAcc #-}

instance FFoldable V1 where
  flengthAcc _ = \case
  {-# inline flengthAcc #-}

instance FFoldable (K1 i a) where
  flengthAcc = const
  {-# inline flengthAcc #-}

deriving newtype instance FFoldable f => FFoldable (M1 i c f)
deriving newtype instance FFoldable f => FFoldable (Rec1 f)

instance FFoldable U1 where
  flengthAcc = const
  {-# inline flengthAcc #-}

instance (Foldable f, FFoldable g) => FFoldable (f :.: g) where
  ffoldMap f = foldMap (ffoldMap f) .# unComp1
  {-# inline ffoldMap #-}

instance (FFoldable f, FFoldable g) => FFoldable (f :*: g) where
  ffoldMap f (g :*: h) = ffoldMap f g `mappend` ffoldMap f h
  flengthAcc acc (g :*: h) = acc `flengthAcc` g `flengthAcc` h
  {-# inline ffoldMap #-}
  {-# inline flengthAcc #-}

instance (FFoldable f, FFoldable g) => FFoldable (f :+: g) where
  ffoldMap f (L1 g) = ffoldMap f g
  ffoldMap f (R1 h) = ffoldMap f h
  flengthAcc acc (L1 g) = flengthAcc acc g
  flengthAcc acc (R1 g) = flengthAcc acc g
  {-# inline ffoldMap #-}
  {-# inline flengthAcc #-}

-------------------------------------------------------------------------------
-- FTraversable
-------------------------------------------------------------------------------

class (FFoldable t, FFunctor t) => FTraversable (t :: (k -> Type) -> Type) where
  ftraverse :: Applicative m => (forall a. f a -> m (g a)) -> t f -> m (t g)
  default ftraverse
    :: forall f g m. (Generic1 t, FTraversable (Rep1 t), Applicative m)
    => (forall a. f a -> m (g a)) -> t f -> m (t g)
  ftraverse = fconfusing (\nt -> fmap to1 . ftraverse nt . from1)
  {-# inline ftraverse #-}

ffmapDefault :: FTraversable t =>  (f ~> g) -> t f -> t g
ffmapDefault k = runIdentity #. ftraverse (Identity #. k)
{-# inline ffmapDefault #-}

ffoldMapDefault :: (FTraversable t, Monoid m) =>  (forall a. f a -> m) -> t f -> m
ffoldMapDefault k = getConst #. ftraverse (Const #. k)
{-# inline ffoldMapDefault #-}

ffor :: (FTraversable t, Applicative m) => t f -> (forall a. f a -> m (g a)) -> m (t g)
ffor tf k = ftraverse k tf
{-# inline ffor #-}

fsequence :: (FTraversable t, Applicative f) => t f -> f (t Identity)
fsequence = ftraverse (fmap Identity)
{-# inline fsequence #-}

instance FTraversable Proxy where
  ftraverse _ Proxy = pure Proxy
  {-# inline ftraverse #-}

instance FTraversable (Const a) where
  ftraverse _ = pure .# (Const . getConst)
  {-# inline ftraverse #-}

instance FTraversable (Constant a) where
  ftraverse _ = pure .# (Constant . getConstant)
  {-# inline ftraverse #-}

instance (Traversable f, FTraversable g) => FTraversable (Compose f g) where
  ftraverse f = fmap Compose . traverse (ftraverse f) .# getCompose
  {-# inline ftraverse #-}

instance (FTraversable f, FTraversable g) => FTraversable (Product f g) where
  ftraverse f (Pair g h) = Pair <$> ftraverse f g <*> ftraverse f h
  {-# inline ftraverse #-}

instance (FTraversable f, FTraversable g) => FTraversable (Sum f g) where
  ftraverse f (InL g) = InL <$> ftraverse f g
  ftraverse f (InR h) = InR <$> ftraverse f h
  {-# inline ftraverse #-}

instance FTraversable U1 where
  ftraverse _ U1 = pure U1
  {-# inline ftraverse #-}

instance FTraversable V1 where
  ftraverse _ = \case
  {-# inline ftraverse #-}

instance FTraversable f => FTraversable (M1 i c f) where
  ftraverse f = fmap M1 . ftraverse f .# unM1
  {-# inline ftraverse #-}

instance FTraversable f => FTraversable (Rec1 f) where
  ftraverse f = fmap Rec1 . ftraverse f .# unRec1
  {-# inline ftraverse #-}

instance FTraversable (K1 i a) where
  ftraverse _ = pure .# (K1 . unK1)
  {-# inline ftraverse #-}

instance (Traversable f, FTraversable g) => FTraversable (f :.: g) where
  ftraverse f = fmap Comp1 . traverse (ftraverse f) .# unComp1
  {-# inline ftraverse #-}

instance (FTraversable f, FTraversable g) => FTraversable (f :*: g) where
  ftraverse f (g :*: h) = (:*:) <$> ftraverse f g <*> ftraverse f h
  {-# inline ftraverse #-}

instance (FTraversable f, FTraversable g) => FTraversable (f :+: g) where
  ftraverse f (L1 g) = L1 <$> ftraverse f g
  ftraverse f (R1 h) = R1 <$> ftraverse f h
  {-# inline ftraverse #-}

-------------------------------------------------------------------------------
-- FZip
-------------------------------------------------------------------------------

class FFunctor t => FZip t where
  fzipWith :: (forall x. f x -> g x -> h x) -> t f -> t g -> t h
  default fzipWith :: (Generic1 t, FZip (Rep1 t)) => (forall x. f x -> g x -> h x) -> t f -> t g -> t h
  fzipWith nt x y = to1 (fzipWith nt (from1 x) (from1 y))
  {-# inline fzipWith #-}

class FZip t => FRepeat t where
  frepeat :: (forall x. f x) -> t f
  default frepeat :: (Generic1 t, FRepeat (Rep1 t)) => (forall x. f x) -> t f 
  frepeat fx = to1 $ frepeat fx
  {-# inline frepeat #-}

instance FZip Proxy where
  fzipWith _ _ _ = Proxy
  {-# inline fzipWith #-}

instance FRepeat Proxy where
  frepeat _ = Proxy
  {-# inline frepeat #-}

instance FZip Limit where
  fzipWith f (Limit x) (Limit y) = Limit (f x y)
  {-# inline fzipWith #-}

instance FRepeat Limit where
  frepeat x = Limit x
  {-# inline frepeat #-}

instance Data.Semigroup.Semigroup a => FZip (Const a) where
  fzipWith _ (Const a) (Const b) = Const (a <> b)
  {-# inline fzipWith #-}

instance (Monoid a, Semigroup a) => FRepeat (Const a) where
  frepeat _ = Const mempty
  {-# inline frepeat #-}

instance (FZip f, FZip g) => FZip (Product f g) where
  fzipWith f (Pair x y) (Pair x' y') = Pair (fzipWith f x x') (fzipWith f y y')
  {-# inline fzipWith #-}

instance (FRepeat f, FRepeat g) => FRepeat (Product f g) where
  frepeat x = Pair (frepeat x) (frepeat x)
  {-# inline frepeat #-}

-- | We only need an 'Apply' part of an 'Applicative'.
instance (Applicative f, FZip g) => FZip (Compose f g) where
  fzipWith f (Compose x) (Compose y) = Compose (liftA2 (fzipWith f) x y)
  {-# inline fzipWith #-}

instance (Applicative f, FRepeat g) => FRepeat (Compose f g) where
  frepeat x = Compose (pure (frepeat x))
  {-# inline frepeat #-}

instance FZip U1 where
  fzipWith _ _ _ =  U1
  {-# inline fzipWith #-}

instance FRepeat U1 where
  frepeat _ = U1
  {-# inline frepeat #-}

instance FZip V1 where
  fzipWith _ x _ = case x of
  {-# inline fzipWith #-}

instance FZip f => FZip (M1 i c f) where
  fzipWith f (M1 x) (M1 y) = M1 $ fzipWith f x y
  {-# inline fzipWith #-}

instance FZip f => FZip (Rec1 f) where
  fzipWith f (Rec1 x) (Rec1 y) = Rec1 $ fzipWith f x y
  {-# inline fzipWith #-}

instance Data.Semigroup.Semigroup a => FZip (K1 i a) where
  fzipWith _ (K1 a) (K1 b) = K1 (a <> b)
  {-# inline fzipWith #-}

instance (Monoid a, Semigroup a) => FRepeat (K1 i a) where
  frepeat _ = K1 mempty
  {-# inline frepeat #-}

instance FRepeat f => FRepeat (M1 i c f) where
  frepeat x = M1 $ frepeat x
  {-# inline frepeat #-}

instance FRepeat f => FRepeat (Rec1 f) where
  frepeat x = Rec1 $ frepeat x
  {-# inline frepeat #-}

instance (FZip f, FZip g) => FZip (f :*: g) where
  fzipWith f (x :*: y) (x' :*: y') = fzipWith f x x' :*: fzipWith f y y'
  {-# inline fzipWith #-}

instance (FRepeat f, FRepeat g) => FRepeat (f :*: g) where
  frepeat x = frepeat x :*: frepeat x
  {-# inline frepeat #-}

-- | We only need an 'Apply' part of an 'Applicative'.
instance (Applicative f, FZip g) => FZip (f :.: g) where
  fzipWith f (Comp1 x) (Comp1 y) = Comp1 (liftA2 (fzipWith f) x y)
  {-# inline fzipWith #-}

instance (Applicative f, FRepeat g) => FRepeat (f :.: g) where
  frepeat x = Comp1 (pure (frepeat x))
  {-# inline frepeat #-}

deriving newtype instance FFunctor f => FFunctor (Backwards f)
deriving newtype instance FFunctor f => FFunctor (Reverse f)
deriving newtype instance FFunctor f => FFunctor (Monoid.Alt f)

-- to match the behavior on Appliative
instance FZip f => FZip (Backwards f) where
  fzipWith = \f (Backwards xs) (Backwards ys) -> Backwards $ fzipWith (\j k -> f k j) ys xs
  {-# inline fzipWith #-}

deriving newtype instance FZip f => FZip (Reverse f)
deriving newtype instance FZip f => FZip (Monoid.Alt f)
deriving newtype instance FRepeat f => FRepeat (Backwards f)
deriving newtype instance FRepeat f => FRepeat (Reverse f)
deriving newtype instance FRepeat f => FRepeat (Monoid.Alt f)
deriving newtype instance FFoldable f => FFoldable (Backwards f)
deriving newtype instance FFoldable f => FFoldable (Monoid.Alt f)

instance FFoldable f => FFoldable (Reverse f) where
  ffoldMap = \f -> Monoid.getDual #. ffoldMap (Monoid.Dual #. f)
  {-# inline ffoldMap #-}

instance FTraversable f => FTraversable (Reverse f) where
  ftraverse = \f -> forwards #. fmap Reverse . ftraverse (Backwards #. f) .# getReverse
  {-# inline ftraverse #-}

instance FTraversable f => FTraversable (Backwards f) where
  ftraverse = \f -> fmap Backwards . ftraverse f .# forwards
  {-# inline ftraverse #-}

instance FTraversable f => FTraversable (Monoid.Alt f) where
  ftraverse = \f -> fmap Monoid.Alt . ftraverse f .# Monoid.getAlt 
  {-# inline ftraverse #-}
  
deriving newtype instance FFunctor f => FFunctor (Monoid.Ap f)
deriving newtype instance FZip f => FZip (Monoid.Ap f)
deriving newtype instance FRepeat f => FRepeat (Monoid.Ap f)
deriving newtype instance FFoldable f => FFoldable (Monoid.Ap f)

instance FTraversable f => FTraversable (Monoid.Ap f) where
  ftraverse = \f -> fmap Monoid.Ap . ftraverse f .# Monoid.getAp
  {-# inline ftraverse #-}

-- * F0

type role F0 phantom
data F0 f = F0
  deriving stock (Generic, Generic1, Functor, Foldable, Traversable)
  deriving anyclass (FFunctor, FFoldable, FTraversable, FRepeat, FZip)

-- * F1

type role F1 nominal representational
newtype F1 a f = F1 { runF1 :: f a }
  deriving anyclass FFunctor

instance FFoldable (F1 a) where
  ffoldMap f = f .# runF1
  flengthAcc acc _ = acc + 1
  {-# inline ffoldMap #-}
  {-# inline flengthAcc #-}

instance FTraversable (F1 a) where
  ftraverse f = fmap F1 . f .# runF1
  {-# inline ftraverse #-}

instance FRepeat (F1 a) where
  frepeat x = F1 x

instance FZip (F1 a) where
  fzipWith f (F1 a) (F1 b) = F1 (f a b)

type role F2 nominal nominal representational
data F2 a b f = F2 (f a) (f b)
  deriving anyclass FFunctor

instance FFoldable (F2 a b) where
  flengthAcc acc _ = acc + 2
  {-# inline flengthAcc #-}

instance FTraversable (F2 a b) where
  ftraverse = \f (F2 a b) -> liftA2 F2 (f a) (f b)
  {-# inline ftraverse #-}

instance FZip (F2 a b) where
  fzipWith = \f (F2 a b) (F2 a' b') -> F2 (f a a') (f b b')
  {-# inline fzipWith #-}

instance FRepeat (F2 a b) where
  frepeat = \x -> F2 x x
  {-# inline frepeat #-}

type role F3 nominal nominal nominal representational
data F3 a b c f = F3 (f a) (f b) (f c)
  deriving anyclass FFunctor

instance FFoldable (F3 a b c) where
  flengthAcc = \acc _ -> acc + 3
  {-# inline flengthAcc #-}

instance FTraversable (F3 a b c) where
  ftraverse = \f (F3 a b c) -> liftA2 F3 (f a) (f b) <*> f c
  {-# inline ftraverse #-}

instance FZip (F3 a b c) where
  fzipWith = \f (F3 a b c) (F3 a' b' c') -> F3 (f a a') (f b b') (f c c')
  {-# inline fzipWith #-}

instance FRepeat (F3 a b c) where
  frepeat = \x -> F3 x x x 
  {-# inline frepeat #-}

type role F4 nominal nominal nominal nominal representational
data F4 a b c d f = F4 (f a) (f b) (f c) (f d)
  deriving anyclass FFunctor

instance FFoldable (F4 a b c d) where
  flengthAcc = \acc _ -> acc + 4
  {-# inline flengthAcc #-}

instance FTraversable (F4 a b c d) where
  ftraverse = \f (F4 a b c d) -> liftA2 F4 (f a) (f b) <*> f c <*> f d
  {-# inline ftraverse #-}

instance FZip (F4 a b c d) where
  fzipWith = \f (F4 a b c d) (F4 a' b' c' d') -> F4 (f a a') (f b b') (f c c') (f d d')
  {-# inline fzipWith #-}

instance FRepeat (F4 a b c d) where
  frepeat = \x -> F4 x x x x
  {-# inline frepeat #-}

type role F5 nominal nominal nominal nominal nominal representational
data F5 a b c d e f = F5 (f a) (f b) (f c) (f d) (f e)
  deriving anyclass FFunctor

instance FFoldable (F5 a b c d e) where
  flengthAcc = \acc _ -> acc + 5
  {-# inline flengthAcc #-}

instance FTraversable (F5 a b c d e) where
  ftraverse = \f (F5 a b c d e) -> liftA2 F5 (f a) (f b) <*> f c <*> f d <*> f e
  {-# inline ftraverse #-}

instance FZip (F5 a b c d e) where
  fzipWith = \f (F5 a b c d e) (F5 a' b' c' d' e') -> F5 (f a a') (f b b') (f c c') (f d d') (f e e')
  {-# inline fzipWith #-}

instance FRepeat (F5 a b c d e) where
  frepeat = \x -> F5 x x x x x
  {-# inline frepeat #-}

-------------------------------------------------------------------------------
-- "natural" transformations via parametricity
-------------------------------------------------------------------------------

-- | Newtyped "natural" transformation
newtype NT f g = NT { runNT :: f ~> g }

instance FFunctor (NT f) where
  ffmap = \f (NT g) -> NT (f . g)
  {-# inline ffmap #-}

instance FZip (NT f) where
  fzipWith = \f (NT g) (NT h) -> NT \x -> f (g x) (h x)
  {-# inline fzipWith #-}

instance FRepeat (NT a) where
  frepeat = \x -> NT \_ -> x
  {-# inline frepeat #-}

-------------------------------------------------------------------------------
-- Some
-------------------------------------------------------------------------------

instance FFunctor Some where
  ffmap = mapSome
  {-# inline ffmap #-}

instance FFoldable Some where
  ffoldMap = foldSome
  flengthAcc len _ = len + 1
  {-# inline ffoldMap #-}
  {-# inline flengthAcc #-}

instance FTraversable Some where
  ftraverse f (Some m) = Some <$> f m
  {-# inline ftraverse #-}

instance FFunctor G.Some where
  ffmap = G.mapSome
  {-# inline ffmap #-}

instance FFoldable G.Some where
  ffoldMap = G.foldSome
  flengthAcc len _ = len + 1
  {-# inline ffoldMap #-}
  {-# inline flengthAcc #-}

instance FTraversable G.Some where
  ftraverse f x = G.withSome x $ fmap G.Some . f
  {-# inline ftraverse #-}

instance FFunctor C.Some where
  ffmap = C.mapSome
  {-# inline ffmap #-}

instance FFoldable C.Some where
  ffoldMap = C.foldSome
  flengthAcc len _ = len + 1
  {-# inline ffoldMap #-}
  {-# inline flengthAcc #-}

instance FTraversable C.Some where
  ftraverse f x = C.withSome x $ fmap C.mkSome . f
  {-# inline ftraverse #-}

-------------------------------------------------------------------------------
-- Limit
-------------------------------------------------------------------------------

newtype Limit f = Limit
  { runLimit :: forall a. f a
  }

instance FFunctor Limit where
  ffmap f (Limit g) = Limit (f g)
  {-# inline ffmap #-}

instance FFoldable Limit where
  ffoldMap f (Limit g) = f g
  flengthAcc len _ = len + 1
  {-# inline ffoldMap #-}
  {-# inline flengthAcc #-}

instance FTraversable Limit where
  ftraverse = \ f (Limit m) -> unsafeCoerce <$> f m
  {-# inline ftraverse #-}

-- * Dicts

data Dict1 p a where
  Dict1 :: p a => Dict1 p a

newtype Dicts p f = Dicts
  { runDicts :: f (Dict1 p)
  }

instance FFunctor (Dicts p) where
  ffmap = \ f -> Dicts #. f .# runDicts
  {-# inline ffmap #-}

newtype FConstrained p f = FConstrained
  { runFConstrained :: forall x. p x => f x
  }

instance FFunctor (FConstrained p) where
  ffmap = \f x -> FConstrained (f $ runFConstrained x)
  {-# inline ffmap #-}

instance (forall x. p x) => FFoldable (FConstrained p) where
  ffoldMap = \ f x -> f $ runFConstrained x
  {-# inline ffoldMap #-}

-- instance (forall x. p x) => FTraversable (FConstrained p) where

type role FCompose nominal representational nominal
newtype FCompose a f g = FCompose { runFCompose :: f (g a) }

instance Functor f => FFunctor (FCompose a f) where
  ffmap = \f -> FCompose #. (fmap f .# runFCompose)
  {-# inline ffmap #-}

instance Foldable f => FFoldable (FCompose a f) where
  ffoldMap = \f -> foldMap f .# runFCompose
  {-# inline ffoldMap #-}

instance Traversable f => FTraversable (FCompose a f) where
  ftraverse = \f -> fmap FCompose . traverse f .# runFCompose 
  {-# inline ftraverse #-}
