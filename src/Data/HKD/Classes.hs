{-# Language GeneralizedNewtypeDeriving #-}
{-# language Trustworthy #-}

-- |
-- Copyright :  (c) 2019-2021 Edward Kmett
--              (c) 2019 Oleg Grenrus
--              (c) 2017-2021 Aaron Vargo
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
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
-- Generically derived 'FApply' and 'FApplicative':
--
-- @
-- data Record f = Record
--   { fieldInt    :: f Int
--   , fieldString :: f String
--   } deriving ('Generic1', 'FApply', 'FApplicative')
-- @
module Data.HKD.Classes
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
, ViaFTraversable(..)
, ffmapDefault
, ffoldMapDefault
, ffor
, fsequence
, FApply(..)
, FApplicative(..)
, ViaFApplicative(..)
-- * FMonad
, FMonad(..)
, ViaFMonad(..)
, fbindInner
, fbindOuter
-- * FEq
, EqC, FEq
-- * FOrd
, OrdC', OrdC, FOrd
) where

import Control.Applicative
import Control.Applicative.Backwards
import Control.Monad(join)
import Data.Proxy (Proxy (..))
import Data.Coerce (coerce)
import Data.Functor.Constant
import Data.Functor.Compose (Compose (..))
import Data.Functor.Identity (Identity (..))
import Data.Functor.Product (Product (..))
import Data.Functor.Rep.Internal.Coerce
import Data.Functor.Reverse
import Data.Functor.Sum (Sum (..))
import qualified Data.Monoid as Monoid
import Data.Kind (Type, Constraint)
import qualified Data.Some.GADT as G
import Data.Some.Newtype (Some (..), mapSome, foldSome, withSome)
import qualified Data.Some.Church as C
import Data.Traversable.Confusing
import GHC.Generics

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

-- | For use with DerivingVia
newtype ViaFTraversable t f = ViaFTraversable { runViaFTraversable :: t f }

instance FTraversable t => FFunctor (ViaFTraversable t) where
  ffmap = \f -> ViaFTraversable #. ffmapDefault f .# runViaFTraversable
  {-# inline ffmap #-}

instance FTraversable t => FFoldable (ViaFTraversable t) where
  ffoldMap = \f -> ffoldMapDefault f .# runViaFTraversable
  {-# inline ffoldMap #-}

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
-- FApply
-------------------------------------------------------------------------------

class FFunctor t => FApply t where
  fliftA2 :: (forall x. f x -> g x -> h x) -> t f -> t g -> t h
  default fliftA2 :: (Generic1 t, FApply (Rep1 t)) => (forall x. f x -> g x -> h x) -> t f -> t g -> t h
  fliftA2 nt x y = to1 (fliftA2 nt (from1 x) (from1 y))
  {-# inline fliftA2 #-}

class FApply t => FApplicative t where
  fpure :: (forall x. f x) -> t f
  default fpure :: (Generic1 t, FApplicative (Rep1 t)) => (forall x. f x) -> t f
  fpure fx = to1 $ fpure fx
  {-# inline fpure #-}

-- | For use with DerivingVia
newtype ViaFApplicative t f = ViaFApplicative { runViaFApplicative :: t f }

instance FApply t => FFunctor (ViaFApplicative t) where
  ffmap = \f -> ViaFApplicative #. join (fliftA2 (const f)) .# runViaFApplicative
  {-# inline ffmap #-}

instance FApply Proxy where
  fliftA2 _ _ _ = Proxy
  {-# inline fliftA2 #-}

instance FApplicative Proxy where
  fpure _ = Proxy
  {-# inline fpure #-}

instance Semigroup a => FApply (Const a) where
  fliftA2 _ (Const a) (Const b) = Const (a <> b)
  {-# inline fliftA2 #-}

instance Monoid a => FApplicative (Const a) where
  fpure _ = Const mempty
  {-# inline fpure #-}

instance (FApply f, FApply g) => FApply (Product f g) where
  fliftA2 f (Pair x y) (Pair x' y') = Pair (fliftA2 f x x') (fliftA2 f y y')
  {-# inline fliftA2 #-}

instance (FApplicative f, FApplicative g) => FApplicative (Product f g) where
  fpure x = Pair (fpure x) (fpure x)
  {-# inline fpure #-}

-- | We only need an 'Apply' part of an 'Applicative'.
instance (Applicative f, FApply g) => FApply (Compose f g) where
  fliftA2 f (Compose x) (Compose y) = Compose (liftA2 (fliftA2 f) x y)
  {-# inline fliftA2 #-}

instance (Applicative f, FApplicative g) => FApplicative (Compose f g) where
  fpure x = Compose (pure (fpure x))
  {-# inline fpure #-}

instance FApply U1 where
  fliftA2 _ _ _ =  U1
  {-# inline fliftA2 #-}

instance FApplicative U1 where
  fpure _ = U1
  {-# inline fpure #-}

instance FApply V1 where
  fliftA2 _ x _ = case x of
  {-# inline fliftA2 #-}

instance FApply f => FApply (M1 i c f) where
  fliftA2 f (M1 x) (M1 y) = M1 $ fliftA2 f x y
  {-# inline fliftA2 #-}

instance FApply f => FApply (Rec1 f) where
  fliftA2 f (Rec1 x) (Rec1 y) = Rec1 $ fliftA2 f x y
  {-# inline fliftA2 #-}

instance Semigroup a => FApply (K1 i a) where
  fliftA2 _ (K1 a) (K1 b) = K1 (a <> b)
  {-# inline fliftA2 #-}

instance Monoid a => FApplicative (K1 i a) where
  fpure _ = K1 mempty
  {-# inline fpure #-}

deriving newtype instance FApplicative f => FApplicative (M1 i c f)
deriving newtype instance FApplicative f => FApplicative (Rec1 f)

instance (FApply f, FApply g) => FApply (f :*: g) where
  fliftA2 f (x :*: y) (x' :*: y') = fliftA2 f x x' :*: fliftA2 f y y'
  {-# inline fliftA2 #-}

instance (FApplicative f, FApplicative g) => FApplicative (f :*: g) where
  fpure x = fpure x :*: fpure x
  {-# inline fpure #-}

-- | We only need an 'Apply' part of an 'Applicative'.
instance (Applicative f, FApply g) => FApply (f :.: g) where
  fliftA2 f (Comp1 x) (Comp1 y) = Comp1 (liftA2 (fliftA2 f) x y)
  {-# inline fliftA2 #-}

instance (Applicative f, FApplicative g) => FApplicative (f :.: g) where
  fpure x = Comp1 (pure (fpure x))
  {-# inline fpure #-}

deriving newtype instance FFunctor f => FFunctor (Backwards f)
deriving newtype instance FFunctor f => FFunctor (Reverse f)
deriving newtype instance FFunctor f => FFunctor (Monoid.Alt f)

-- to match the behavior on Appliative
instance FApply f => FApply (Backwards f) where
  fliftA2 = \f (Backwards xs) (Backwards ys) -> Backwards $ fliftA2 (\j k -> f k j) ys xs
  {-# inline fliftA2 #-}

deriving newtype instance FApply f => FApply (Reverse f)
deriving newtype instance FApply f => FApply (Monoid.Alt f)
deriving newtype instance FApplicative f => FApplicative (Backwards f)
deriving newtype instance FApplicative f => FApplicative (Reverse f)
deriving newtype instance FApplicative f => FApplicative (Monoid.Alt f)
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
deriving newtype instance FApply f => FApply (Monoid.Ap f)
deriving newtype instance FApplicative f => FApplicative (Monoid.Ap f)
deriving newtype instance FFoldable f => FFoldable (Monoid.Ap f)

instance FTraversable f => FTraversable (Monoid.Ap f) where
  ftraverse = \f -> fmap Monoid.Ap . ftraverse f .# Monoid.getAp
  {-# inline ftraverse #-}

-- * FMonad

-- fjoin :: f (f :.: b) -> f (Join b)
class FApplicative f => FMonad f where
  fbind :: (forall x. b x x -> r x) -> f a -> (forall x. a x -> f (b x)) -> f r

newtype Inner a x y = Inner { runInner :: a y }

-- TODO: avoid the ffmap coerces

-- | 'fbind' with @b@ indexed only on the inner layer
fbindInner :: FMonad f => f a -> (forall x. a x -> f b) -> f b
fbindInner = \fa f -> fbind runInner fa \a -> ffmap Inner $ f a
{-# inline fbindInner #-}

newtype Outer a x y = Outer { runOuter :: a x }

-- | 'fbind' with @b@ indexed only on the outer layer
fbindOuter :: FMonad f => f a -> (forall x. a x -> f (Const (b x))) -> f b
fbindOuter = \fa f -> fbind runOuter fa \a -> ffmap coerce $ f a
{-# inline fbindOuter #-}


fliftM :: FMonad f => (a ~> b) -> f a -> f b
fliftM = \f fa -> fbind runOuter fa \a -> fpure $ Outer $ f a
{-# inline fliftM #-}

newtype LiftM2 a x y = LiftM2 (x ~ y => a x)

fliftM2 :: FMonad f => (forall x. a x -> b x -> c x) -> f a -> f b -> f c
fliftM2 = \f fa fb -> fbind (\(LiftM2 x) -> x) fa \a -> ffmap (\b -> LiftM2 $ f a b) fb
{-# inline fliftM2 #-}

newtype ViaFMonad f a = ViaFMonad { runViaFMonad :: f a }

-- | Derive FFunctor from fbind and fpure
instance FMonad f => FFunctor (ViaFMonad f) where
  ffmap = \f -> ViaFMonad #. fliftM f .# runViaFMonad
  {-# inline ffmap #-}

-- | Derive FApply from fbind and ffmap
instance FMonad f => FApply (ViaFMonad f) where
  fliftA2 = \f (ViaFMonad fa) -> ViaFMonad #. fliftM2 f fa .# runViaFMonad
  {-# inline fliftA2 #-}

-- | Eq constraints on `k`
type family EqC :: k -> Constraint

type instance EqC @Type = Eq

class (forall x. EqC x => Eq (w x)) => FEq w
instance (forall x. EqC x => Eq (w x)) => FEq w

type instance EqC @(k -> Type) = FEq

-- | Ord constraints on `k`
type family OrdC' :: k -> Constraint

type instance OrdC' @Type = Ord

class (FEq w, forall x. OrdC x => Ord (w x)) => FOrd w
instance (FEq w, forall x. OrdC x => Ord (w x)) => FOrd w

type instance OrdC' @(k -> Type) = FOrd

class (EqC x, OrdC' x) => OrdC x where
instance (EqC x, OrdC' x) => OrdC x where

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
