{-# Language CPP #-}
{-# Language GeneralizedNewtypeDeriving #-}
{-# Language TypeApplications #-}
{-# Language Trustworthy #-}

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
, ftoList
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
, FFunctorWithIndex(..)
, ifmapDefault
, FFoldableWithIndex(..)
, iffoldMapDefault
, iftoList
, FTraversableWithIndex(..)
, FApply(..)
, FApplicative(..)
, ViaFApplicative(..)
-- * FBind
, Coatkey(..)
, runCoatkey
, FBind(..)
, ViaFBind(..)
, FMonad
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
import Data.Coerce
import qualified Data.Dependent.HashMap as DHashMap
import Data.Dependent.HashMap (DHashMap)
import Data.Dependent.Sum
import Data.Foldable.WithIndex
import Data.Function.Coerce
import Data.Functor.Constant
import Data.Functor.Compose (Compose (..))
import Data.Functor.Identity (Identity (..))
import Data.Functor.Product (Product (..))
import Data.Functor.Reverse
import Data.Functor.Sum (Sum (..))
import Data.Functor.WithIndex
import Data.GADT.Compare
import Data.Hashable
import Data.HKD.Orphans ()
import Data.Kind (Type, Constraint)
import qualified Data.Monoid as Monoid
import Data.Proxy (Proxy (..))
import qualified Data.Some.GADT as G
import Data.Some.Newtype (Some (..), mapSome, foldSome, withSome, traverseSome)
import qualified Data.Some.Church as C
import Data.Traversable.Confusing
import Data.Traversable.WithIndex
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

instance FFunctor (DHashMap f) where
  ffmap = DHashMap.map
  {-# inline ffmap #-}

instance FFunctor (DSum f) where
  ffmap f (g :=> h) = g :=> f h
  {-# inline ffmap #-}

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

ftoList :: FFoldable t => t f -> [Some f]
ftoList = ffoldMap (\x -> [Some x])
{-# inline ftoList #-}

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

instance FFoldable (DSum f) where
  ffoldMap f (_ :=> h) = f h
  {-# inline ffoldMap #-}
  flengthAcc n _ = n + 1
  {-# inline flengthAcc #-}

instance FFoldable (DHashMap f) where
  ffoldMap = DHashMap.foldMap
  {-# inline ffoldMap #-}
  flengthAcc n m = n + DHashMap.size m
  {-# inline flengthAcc #-}

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

instance FTraversable (DSum f) where
  ftraverse f (g :=> h) = (g :=>) <$> f h
  {-# inline ftraverse #-}

instance FTraversable (DHashMap f) where
  ftraverse = DHashMap.traverse
  {-# inline ftraverse #-}

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

instance (GEq f, Hashable (Some f)) => FApply (DHashMap f) where
  fliftA2 = DHashMap.intersectionWith
  {-# inline fliftA2 #-}

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

-- * FBind

newtype Coatkey a x y = Coatkey (x ~ y => a x)

runCoatkey :: Coatkey a x x -> a x
runCoatkey = \(Coatkey a) -> a
{-# inline runCoatkey #-}

class FApply f => FBind f where
  fbind :: f a -> (forall x. a x -> f (Coatkey b x)) -> f b

-- | 'fbind' indexed only on the inner layer
fbindInner :: FBind f => f a -> (forall x. a x -> f b) -> f b
fbindInner = \fa f -> fbind fa \a -> ffmap (\x -> Coatkey x) $ f a
{-# inline fbindInner #-}

-- | 'fbind' indexed only on the outer layer
fbindOuter :: FBind f => f a -> (forall x. a x -> f (Const (b x))) -> f b
fbindOuter = \fa f -> fbind fa \a -> ffmap (\x -> Coatkey (getConst x)) $ f a
{-# inline fbindOuter #-}

newtype ViaFBind f a = ViaFBind { runViaFBind :: f a }
  deriving newtype FFunctor

-- | Derive 'FApply' from 'fbind' and 'ffmap'
instance FBind f => FApply (ViaFBind f) where
  fliftA2 = \f (ViaFBind fa) -> ViaFBind #. fliftM2 f fa .# runViaFBind
  {-# inline fliftA2 #-}

-- |
-- 'Applicative and Bind are enough to show 'Monad'
--
-- @
-- fa
-- = pure id <*> fa
-- = join $ fmap (\f -> f <$> fa) (pure id)
-- = join $ pure $ id <$> fa
-- = join $ pure fa
-- @
--
-- @
-- fa
-- = fa <* pure ()
-- = liftA2 const fa (pure ())
-- = join $ fmap (\a -> const a <$> pure ()) fa
-- = join $ fmap (\a -> pure (const a ())) fa
-- = join $ fmap pure fa
-- @
--
-- Likewise, 'FApplicative' and 'FBind' are enough to show 'FMonad' :
--
-- @
-- fa
-- = fliftA2 const fa (fpure Proxy)
-- = fbind fa \a -> ffmap (\x -> Coatkey $ const a x) (fpure Proxy)
-- = fbind fa \a -> ffmap (const $ Coatkey a) (fpure Proxy)
-- = fbind fa \a -> fpure (Coatkey a)
--
-- fa
-- = fliftA2 (flip const) (fpure Proxy) fa
-- = fbind (fpure Proxy) \x -> ffmap (\a -> Coatkey $ flip const x a) fa
-- = fbind (fpure Proxy) \_ -> ffmap (\a -> Coatkey a) fa
-- = fbind (fpure (Const fa)) (\(Const fa') -> ffmap Coatkey fa')
-- @
class (FApplicative f, FBind f) => FMonad f
instance (FApplicative f, FBind f) => FMonad f

-- _proof :: forall f a. (FApplicative f, FBind f) => f a -> [f a]
-- _proof fa =
--   [ fa
--   , fliftA2 const fa (fpure Proxy)
--   , fbind fa \a -> ffmap (\x -> Coatkey $ const a x) (fpure Proxy)
--   , fbind fa \a -> ffmap (const $ Coatkey a) (fpure Proxy)
--   , fbind fa \a -> fpure (Coatkey a)

--   , fa
--   , fliftA2 (flip const) (fpure Proxy) fa
--   , fbind (fpure Proxy) \x -> ffmap (\a -> Coatkey $ flip const x a) fa
--   , fbind (fpure Proxy) \_ -> ffmap (\a -> Coatkey a) fa
--   , fbind (fpure (Const fa)) (\(Const ma) -> ffmap Coatkey ma)
--   ]

fliftM :: FMonad f => (a ~> b) -> f a -> f b
fliftM = \f fa -> fbind fa \a -> fpure $ Coatkey $ f a
{-# inline fliftM #-}

fliftM2 :: FBind f => (forall x. a x -> b x -> c x) -> f a -> f b -> f c
fliftM2 = \f fa fb -> fbind fa \a -> ffmap (\b -> Coatkey $ f a b) fb
{-# inline fliftM2 #-}

newtype ViaFMonad f a = ViaFMonad { runViaFMonad :: f a }

-- | Derive 'FFunctor' from 'fbind' and 'fpure'
instance FMonad f => FFunctor (ViaFMonad f) where
  ffmap = \f -> ViaFMonad #. fliftM f .# runViaFMonad
  {-# inline ffmap #-}

-- | Derive 'FApply' from 'fbind' and 'ffmap'
instance FMonad f => FApply (ViaFMonad f) where
  fliftA2 = \f (ViaFMonad fa) -> ViaFMonad #. fliftM2 f fa .# runViaFMonad
  {-# inline fliftA2 #-}

instance (GEq k, Hashable (Some k)) => FBind (DHashMap k) where
  fbind = \m f -> DHashMap.mapMaybeWithKey (\k -> fmap runCoatkey . DHashMap.lookup k . f) m
  {-# inline fbind #-}

-- * WithIndex

class FFunctor f => FFunctorWithIndex i f | f -> i where
  ifmap :: (forall x. i x -> a x -> b x) -> f a -> f b
  default ifmap :: FTraversableWithIndex i f => (forall x. i x -> a x -> b x) -> f a -> f b
  ifmap = ifmapDefault
  {-# inline ifmap #-}

instance FFunctorWithIndex f (DSum f) where
  ifmap f (g :=> h) = g :=> f g h
  {-# inline ifmap #-}

instance FFunctorWithIndex f (DHashMap f) where
  ifmap = DHashMap.mapWithKey
  {-# inline ifmap #-}

ifmapDefault :: FTraversableWithIndex i f => (forall x. i x -> a x -> b x) -> f a -> f b
ifmapDefault = \ f -> runIdentity #. iftraverse (\i a -> Identity (f i a))
{-# inline ifmapDefault #-}

class FFoldable f => FFoldableWithIndex i f | f -> i where
  iffoldMap :: Monoid m => (forall x. i x -> a x -> m) -> f a -> m
  default iffoldMap :: (FTraversableWithIndex i f, Monoid m) => (forall x. i x -> a x -> m) -> f a -> m
  iffoldMap = iffoldMapDefault
  {-# inline iffoldMap #-}

iftoList :: FFoldableWithIndex i t => t f -> [DSum i f]
iftoList = iffoldMap \i a -> [i :=> a]
{-# inline iftoList #-}

iffoldMapDefault :: (FTraversableWithIndex i f, Monoid m) => (forall x. i x -> a x -> m) -> f a -> m
iffoldMapDefault = \f -> getConst #. iftraverse (\i -> Const #. f i)
{-# inline iffoldMapDefault #-}

instance FFoldableWithIndex f (DSum f) where
  iffoldMap f (g :=> h) = f g h
  {-# inline iffoldMap #-}

instance FFoldableWithIndex f (DHashMap f) where
  iffoldMap = DHashMap.foldMapWithKey
  {-# inline iffoldMap #-}

class (FFunctorWithIndex i f, FFoldableWithIndex i f, FTraversable f) => FTraversableWithIndex i f | f -> i where
  iftraverse :: Applicative m => (forall x. i x -> a x -> m (b x)) -> f a -> m (f b)

instance FTraversableWithIndex f (DSum f) where
  iftraverse f (g :=> h) = (g :=>) <$> f g h
  {-# inline iftraverse #-}

instance FTraversableWithIndex f (DHashMap f) where
  iftraverse = DHashMap.traverseWithKey
  {-# inline iftraverse #-}

-- | Eq constraints on `k`
type family EqC :: k -> Constraint


class (forall x. EqC x => Eq (w x)) => FEq w
instance (forall x. EqC x => Eq (w x)) => FEq w

type instance EqC = Eq
type instance EqC = FEq

-- | Ord constraints on `k`
type family OrdC' :: k -> Constraint


class (FEq w, forall x. OrdC x => Ord (w x)) => FOrd w
instance (FEq w, forall x. OrdC x => Ord (w x)) => FOrd w

type instance OrdC' = Ord
type instance OrdC' = FOrd

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

-- TODO: IdentityT

-- * Units

instance FFunctorWithIndex U1 Some where
  ifmap f = mapSome (f U1)

instance FFoldableWithIndex U1 Some where
  iffoldMap f = foldSome (f U1)

instance FTraversableWithIndex U1 Some where
  iftraverse f = traverseSome (f U1)

instance FFunctorWithIndex U1 G.Some where
  ifmap f = G.mapSome (f U1)

instance FFoldableWithIndex U1 G.Some where
  iffoldMap f = G.foldSome (f U1)

instance FTraversableWithIndex U1 G.Some where
  iftraverse f = G.traverseSome (f U1)

instance FFunctorWithIndex U1 C.Some where
  ifmap f = C.mapSome (f U1)

instance FFoldableWithIndex U1 C.Some where
  iffoldMap f = C.foldSome (f U1)

instance FTraversableWithIndex U1 C.Some where
  iftraverse f = C.traverseSome (f U1)

instance FFunctorWithIndex V1 U1 where
  ifmap = \_ U1 -> U1
  {-# inline ifmap #-}

instance FFoldableWithIndex V1 U1 where
  iffoldMap = \_ _ -> mempty
  {-# inline iffoldMap #-}

instance FTraversableWithIndex V1 U1 where
  iftraverse = \_ U1 -> pure U1
  {-# inline iftraverse #-}

instance FFunctorWithIndex V1 Proxy where
  ifmap = \_ _ -> Proxy
  {-# inline ifmap #-}

instance FFoldableWithIndex V1 Proxy where
  iffoldMap = \_ _ -> mempty
  {-# inline iffoldMap #-}

instance FTraversableWithIndex V1 Proxy where
  iftraverse = \_ _ -> pure Proxy
  {-# inline iftraverse #-}
-- * Void

instance FFunctorWithIndex V1 V1 where
  ifmap = \_ -> \case
  {-# inline ifmap #-}

instance FFoldableWithIndex V1 V1 where
  iffoldMap = \_ -> \case
  {-# inline iffoldMap #-}

instance FTraversableWithIndex V1 V1 where
  iftraverse = \_ -> \case
  {-# inline iftraverse #-}

-- * Constants

instance FFunctorWithIndex V1 (Const e) where
  ifmap = \_ -> coerce
  {-# inline ifmap #-}

instance FFoldableWithIndex V1 (Const e) where
  iffoldMap = \_ _ -> mempty
  {-# inline iffoldMap #-}

instance FTraversableWithIndex V1 (Const e) where
  iftraverse = \_ -> pure .# (Const . getConst)
  {-# inline iftraverse #-}

instance FFunctorWithIndex V1 (Constant e) where
  ifmap = \_ -> coerce
  {-# inline ifmap #-}

instance FFoldableWithIndex V1 (Constant e) where
  iffoldMap = \_ _ -> mempty
  {-# inline iffoldMap #-}

instance FTraversableWithIndex V1 (Constant e) where
  iftraverse = \_ -> pure .# (Constant . getConstant)
  {-# inline iftraverse #-}

-- * K1

instance FFunctorWithIndex V1 (K1 i c) where
  ifmap = \_ -> coerce
  {-# inline ifmap #-}

instance FFoldableWithIndex V1 (K1 i c) where
  iffoldMap = \_ _ -> mempty
  {-# inline iffoldMap #-}

instance FTraversableWithIndex V1 (K1 i c) where
  iftraverse = \_ -> pure .# (K1 . unK1)
  {-# inline iftraverse #-}

-- * Products

instance (FFunctorWithIndex i f, FFunctorWithIndex j g) => FFunctorWithIndex (i :+: j) (f :*: g) where
  ifmap = \f (x :*: y) -> ifmap (f . L1) x :*: ifmap (f . R1) y
  {-# inline ifmap #-}

instance (FFoldableWithIndex i f, FFoldableWithIndex j g) => FFoldableWithIndex (i :+: j) (f :*: g) where
  iffoldMap = \f (x :*: y) -> iffoldMap (f . L1) x <> iffoldMap (f . R1) y
  {-# inline iffoldMap #-}

instance (FTraversableWithIndex i f, FTraversableWithIndex j g) => FTraversableWithIndex (i :+: j) (f :*: g) where
  iftraverse = \f (x :*: y) -> liftA2 (:*:) (iftraverse (f . L1) x) (iftraverse (f . R1) y)
  {-# inline iftraverse #-}

instance (FFunctorWithIndex i f, FFunctorWithIndex j g) => FFunctorWithIndex (i :+: j) (Product f g) where
  ifmap = \f (Pair x y) -> Pair (ifmap (f . L1) x) (ifmap (f . R1) y)
  {-# inline ifmap #-}

instance (FFoldableWithIndex i f, FFoldableWithIndex j g) => FFoldableWithIndex (i :+: j) (Product f g) where
  iffoldMap = \f (Pair x y) -> iffoldMap (f . L1) x <> iffoldMap (f . R1) y
  {-# inline iffoldMap #-}

instance (FTraversableWithIndex i f, FTraversableWithIndex j g) => FTraversableWithIndex (i :+: j) (Product f g) where
  iftraverse = \f (Pair x y) -> liftA2 Pair (iftraverse (f . L1) x) (iftraverse (f . R1) y)
  {-# inline iftraverse #-}

-- * Sums

instance (FFunctorWithIndex i f, FFunctorWithIndex j g) => FFunctorWithIndex (i :+: j) (f :+: g) where
  ifmap = \f -> \case
    L1 x -> L1 (ifmap (f . L1) x)
    R1 y -> R1 (ifmap (f . R1) y)
  {-# inline ifmap #-}

instance (FFoldableWithIndex i f, FFoldableWithIndex j g) => FFoldableWithIndex (i :+: j) (f :+: g) where
  iffoldMap = \f -> \case
    L1 x -> iffoldMap (f . L1) x
    R1 y -> iffoldMap (f . R1) y
  {-# inline iffoldMap #-}

instance (FTraversableWithIndex i f, FTraversableWithIndex j g) => FTraversableWithIndex (i :+: j) (f :+: g) where
  iftraverse = \f -> \case
    L1 x -> L1 <$> iftraverse (f . L1) x
    R1 y -> R1 <$> iftraverse (f . R1) y
  {-# inline iftraverse #-}

instance (FFunctorWithIndex i f, FFunctorWithIndex j g) => FFunctorWithIndex (i :+: j) (Sum f g) where
  ifmap = \f -> \case
    InL x -> InL (ifmap (f . L1) x)
    InR y -> InR (ifmap (f . R1) y)
  {-# inline ifmap #-}

instance (FFoldableWithIndex i f, FFoldableWithIndex j g) => FFoldableWithIndex (i :+: j) (Sum f g) where
  iffoldMap = \f -> \case
    InL x -> iffoldMap (f . L1) x
    InR y -> iffoldMap (f . R1) y
  {-# inline iffoldMap #-}

instance (FTraversableWithIndex i f, FTraversableWithIndex j g) => FTraversableWithIndex (i :+: j) (Sum f g) where
  iftraverse = \f -> \case
    InL x -> InL <$> iftraverse (f . L1) x
    InR y -> InR <$> iftraverse (f . R1) y
  {-# inline iftraverse #-}

-- * Composition

instance (FunctorWithIndex i f, FFunctorWithIndex j g) => FFunctorWithIndex (Const i :*: j) (f :.: g) where
  ifmap = \f -> Comp1 #. imap (\i -> ifmap (f . (Const i :*:))) .# unComp1
  {-# inline ifmap #-}

instance (FoldableWithIndex i f, FFoldableWithIndex j g) => FFoldableWithIndex (Const i :*: j) (f :.: g) where
  iffoldMap = \f -> ifoldMap (\i -> iffoldMap (f . (Const i :*:))) .# unComp1
  {-# inline iffoldMap #-}

instance (TraversableWithIndex i f, FTraversableWithIndex j g) => FTraversableWithIndex (Const i :*: j) (f :.: g) where
  iftraverse = \f -> fmap Comp1 . itraverse (\i -> iftraverse (f . (Const i :*:))) .# unComp1
  {-# inline iftraverse #-}

instance (FunctorWithIndex i f, FFunctorWithIndex j g) => FFunctorWithIndex (Const i :*: j) (Compose f g) where
  ifmap = \f -> Compose #. imap (\i -> ifmap (f . (Const i :*:))) .# getCompose
  {-# inline ifmap #-}

instance (FoldableWithIndex i f, FFoldableWithIndex j g) => FFoldableWithIndex (Const i :*: j) (Compose f g) where
  iffoldMap = \f -> ifoldMap (\i -> iffoldMap (f . (Const i :*:))) .# getCompose
  {-# inline iffoldMap #-}

instance (TraversableWithIndex i f, FTraversableWithIndex j g) => FTraversableWithIndex (Const i :*: j) (Compose f g) where
  iftraverse = \f -> fmap Compose . itraverse (\i -> iftraverse (f . (Const i :*:))) .# getCompose
  {-# inline iftraverse #-}

-- * Rec1

deriving newtype instance FFunctorWithIndex i f => FFunctorWithIndex i (Rec1 f)
deriving newtype instance FFoldableWithIndex i f => FFoldableWithIndex i (Rec1 f)
instance FTraversableWithIndex i f => FTraversableWithIndex i (Rec1 f) where
  iftraverse = \f -> fmap Rec1 . iftraverse f .# unRec1
  {-# inline iftraverse #-}

-- * M1

deriving newtype instance FFunctorWithIndex i f => FFunctorWithIndex i (M1 j c f)
deriving newtype instance FFoldableWithIndex i f => FFoldableWithIndex i (M1 j c f)
instance FTraversableWithIndex i f => FTraversableWithIndex i (M1 j c f) where
  iftraverse = \f -> fmap M1 . iftraverse f .# unM1
  {-# inline iftraverse #-}

-- * Alt

deriving newtype instance FFunctorWithIndex i f => FFunctorWithIndex i (Monoid.Alt f)
deriving newtype instance FFoldableWithIndex i f => FFoldableWithIndex i (Monoid.Alt f)
instance FTraversableWithIndex i f => FTraversableWithIndex i (Monoid.Alt f) where
  iftraverse = \f -> fmap Monoid.Alt . iftraverse f .# Monoid.getAlt
  {-# inline iftraverse #-}

-- * Ap

deriving newtype instance FFunctorWithIndex i f => FFunctorWithIndex i (Monoid.Ap f)
deriving newtype instance FFoldableWithIndex i f => FFoldableWithIndex i (Monoid.Ap f)
instance FTraversableWithIndex i f => FTraversableWithIndex i (Monoid.Ap f) where
  iftraverse = \f -> fmap Monoid.Ap . iftraverse f .# Monoid.getAp
  {-# inline iftraverse #-}

-- * Backwards

deriving newtype instance FFunctorWithIndex i f => FFunctorWithIndex i (Backwards f)
deriving newtype instance FFoldableWithIndex i f => FFoldableWithIndex i (Backwards f)
instance FTraversableWithIndex i f => FTraversableWithIndex i (Backwards f) where
  iftraverse = \f -> fmap Backwards . iftraverse f .# forwards
  {-# inline iftraverse #-}

-- * Reverse

deriving newtype instance FFunctorWithIndex i f => FFunctorWithIndex i (Reverse f)
instance FFoldableWithIndex i f => FFoldableWithIndex i (Reverse f) where
  iffoldMap = \f -> Monoid.getDual #. iffoldMap (\i -> Monoid.Dual #. f i) .# getReverse
  {-# inline iffoldMap #-}

instance FTraversableWithIndex i f => FTraversableWithIndex i (Reverse f) where
  iftraverse = \f -> forwards #. fmap Reverse . iftraverse (\i -> Backwards #. f i) .# getReverse
  {-# inline iftraverse #-}
