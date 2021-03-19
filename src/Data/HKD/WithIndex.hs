{-# Language GeneralizedNewtypeDeriving #-}
{-# Language Trustworthy #-}

-- |
-- Copyright :  (c) 2021 Edward Kmett
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable

module Data.HKD.WithIndex 
( FFunctorWithIndex(..)
, ifmapDefault
, FFoldableWithIndex(..)
, iffoldMapDefault
, FTraversableWithIndex(..)
) where
  
import Control.Applicative
import Control.Applicative.Backwards
import Data.Coerce
import Data.Foldable.WithIndex
import Data.Functor.Compose
import Data.Functor.Constant
import Data.Functor.Identity
import Data.Functor.Product
import Data.Functor.Rep.Internal.Coerce
import Data.Functor.Reverse
import Data.Functor.Sum
import Data.Functor.WithIndex
import Data.HKD.Classes
import qualified Data.Monoid as Monoid
import Data.Proxy
import qualified Data.Some.GADT as G
import Data.Some.Newtype (Some(..), mapSome, foldSome, traverseSome)
import qualified Data.Some.Church as C
import Data.Traversable.WithIndex
import GHC.Generics

class FFunctor f => FFunctorWithIndex i f | f -> i where
  ifmap :: (forall x. i x -> a x -> b x) -> f a -> f b
  default ifmap :: FTraversableWithIndex i f => (forall x. i x -> a x -> b x) -> f a -> f b
  ifmap = ifmapDefault
  {-# inline ifmap #-}

ifmapDefault :: FTraversableWithIndex i f => (forall x. i x -> a x -> b x) -> f a -> f b
ifmapDefault = \ f -> runIdentity #. iftraverse (\i a -> Identity (f i a))
{-# inline ifmapDefault #-}

class FFoldable f => FFoldableWithIndex i f | f -> i where
  iffoldMap :: Monoid m => (forall x. i x -> a x -> m) -> f a -> m
  default iffoldMap :: (FTraversableWithIndex i f, Monoid m) => (forall x. i x -> a x -> m) -> f a -> m
  iffoldMap = iffoldMapDefault
  {-# inline iffoldMap #-}

  

-- TODO: IdentityT

iffoldMapDefault :: (FTraversableWithIndex i f, Monoid m) => (forall x. i x -> a x -> m) -> f a -> m
iffoldMapDefault = \f -> getConst #. iftraverse (\i -> Const #. f i)
{-# inline iffoldMapDefault #-}

class (FFunctorWithIndex i f, FFoldableWithIndex i f, FTraversable f) => FTraversableWithIndex i f | f -> i where
  iftraverse :: Applicative m => (forall x. i x -> a x -> m (b x)) -> f a -> m (f b)

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
