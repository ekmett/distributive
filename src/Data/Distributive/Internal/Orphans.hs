{-# Language LambdaCase #-}
{-# Language EmptyCase #-}
{-# Language ScopedTypeVariables #-}
{-# Language PolyKinds #-}
{-# Language DataKinds #-}
{-# Language TypeOperators #-}
{-# Language TypeFamilies #-}
{-# Language InstanceSigs #-}
{-# Language Trustworthy #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Data.Distributive.Internal.Orphans where

import Data.Coerce
import Data.GADT.Compare
import Data.Type.Coercion
import Data.Type.Equality
import GHC.Generics

instance Semigroup (GOrdering a b) where
  GLT <> _ = GLT
  GEQ <> x = x
  GGT <> _ = GGT

instance a ~ b => Monoid (GOrdering a b) where
  mempty = GEQ

instance (GEq f, GEq g) => GEq (f :+: g) where
  geq (L1 x) (L1 y) = geq x y
  geq (R1 x) (R1 y) = geq x y
  geq _ _ = Nothing
  {-# inline geq #-}

instance GEq V1 where
  geq = \case

instance (GEq f, GEq g) => GEq (f :*: g) where
  geq = \(a :*: b) (c :*: d) -> geq a c *> geq b d
  {-# inline geq #-}

instance GEq f => GEq (M1 i c f) where
  geq :: forall a b. M1 i c f a -> M1 i c f b -> Maybe (a :~: b)
  geq = coerce (geq :: f a -> f b -> Maybe (a :~: b))

instance GEq f => GEq (Rec1 f) where
  geq :: forall a b. Rec1 f a -> Rec1 f b -> Maybe (a :~: b)
  geq = coerce (geq :: f a -> f b -> Maybe (a :~: b))

instance (TestEquality f, TestEquality g) => TestEquality (f :+: g) where
  testEquality (L1 x) (L1 y) = testEquality x y
  testEquality (R1 x) (R1 y) = testEquality x y
  testEquality _ _ = Nothing
  {-# inline testEquality #-}

instance (TestEquality f, TestEquality g) => TestEquality (f :*: g) where
  testEquality = \(a :*: b) (c :*: d) -> testEquality a c *> testEquality b d
  {-# inline testEquality #-}

instance TestEquality f => TestEquality (M1 i c f) where
  testEquality :: forall a b. M1 i c f a -> M1 i c f b -> Maybe (a :~: b)
  testEquality = coerce (testEquality :: f a -> f b -> Maybe (a :~: b))

instance TestEquality f => TestEquality (Rec1 f) where
  testEquality :: forall a b. Rec1 f a -> Rec1 f b -> Maybe (a :~: b)
  testEquality = coerce (testEquality :: f a -> f b -> Maybe (a :~: b))

instance TestEquality V1 where
  testEquality = \case

instance (TestCoercion f, TestCoercion g) => TestCoercion (f :+: g) where
  testCoercion (L1 x) (L1 y) = testCoercion x y
  testCoercion (R1 x) (R1 y) = testCoercion x y
  testCoercion _ _ = Nothing
  {-# inline testCoercion #-}

instance (TestCoercion f, TestCoercion g) => TestCoercion (f :*: g) where
  testCoercion = \(a :*: b) (c :*: d) -> testCoercion a c *> testCoercion b d
  {-# inline testCoercion #-}

instance TestCoercion f => TestCoercion (M1 i c f) where
  testCoercion :: forall a b. M1 i c f a -> M1 i c f b -> Maybe (Coercion a b)
  testCoercion = coerce (testCoercion :: f a -> f b -> Maybe (Coercion a b))

instance TestCoercion f => TestCoercion (Rec1 f) where
  testCoercion :: forall a b. Rec1 f a -> Rec1 f b -> Maybe (Coercion a b)
  testCoercion = coerce (testCoercion :: f a -> f b -> Maybe (Coercion a b))

instance TestCoercion V1 where
  testCoercion = \case
