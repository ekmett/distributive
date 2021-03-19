{-# Language Trustworthy #-}
{-# Language GeneralizedNewtypeDeriving #-}
{-# options_ghc -Wno-orphans #-}
{-# options_haddock hide #-}

-- |
-- Copyright   : (C) 2021 Edward Kmett,
-- License     : BSD-2-Clause OR Apache-2.0
-- Maintainer  : Edward Kmett <ekmett@gmail.com>
-- Stability   : provisional
-- Portability : non-portable

module Data.HKD.Orphans () where

import Data.Coerce
import Data.Functor.Classes
import Data.GADT.Compare
import Data.Type.Coercion
import Data.Type.Equality
import GHC.Generics
import Text.Read as Read
-- import GHC.Read (readField)

-- move to base-orphans

instance (Eq1 f, Eq1 g) => Eq1 (f :*: g) where
  liftEq f (a :*: b) (a' :*: b') = liftEq f a a' && liftEq f b b'
  {-# inline liftEq #-}

instance (Ord1 f, Ord1 g) => Ord1 (f :*: g) where
  liftCompare f (a :*: b) (a' :*: b') = liftCompare f a a' <> liftCompare f b b'
  {-# inline liftCompare #-}

instance (Show1 f, Show1 g) => Show1 (f :*: g) where
  -- infixr 6
  liftShowsPrec f l d (x :*: y) =
    showParen (d > 6) $
    liftShowsPrec f l 7 x .
    showString " :*: " .
    liftShowsPrec f l 6 y

instance (Read1 f, Read1 g) => Read1 (f :*: g) where
  liftReadPrec f fl = parens $
    Read.prec 6 $ do
      u <- step (liftReadPrec f fl)
      Symbol ":*:" <- lexP
      (u :*:) <$> step (liftReadPrec f fl)

deriving newtype instance Eq1 f => Eq1 (M1 i c f)
deriving newtype instance Ord1 f => Ord1 (M1 i c f)
deriving newtype instance Show1 f => Show1 (M1 i c f)
deriving newtype instance Read1 f => Read1 (M1 i c f)

instance Eq c => Eq1 (K1 i c) where
  liftEq _ (K1 x) (K1 y) = x == y

instance Ord c => Ord1 (K1 i c) where
  liftCompare _ (K1 x) (K1 y) = compare x y

instance Show c => Show1 (K1 i c) where
  liftShowsPrec _ _ = showsPrec

instance Read c => Read1 (K1 i c) where
  liftReadPrec _ _ = readPrec

instance Eq1 Par1 where
  liftEq f = coerce f 

instance Ord1 Par1 where
  liftCompare f = coerce f

instance Show1 Par1 where
  liftShowsPrec f _ d (Par1 x) = showParen (d > 10) $
    showString "Par1 " . f 11 x
    -- showString "Par1 {unPar1 = " . f d x . showString "}"

-- TODO: use Par1 {unPar1 = ... }
instance Read1 Par1 where
  liftReadPrec f _ = parens $ do
    Read.prec 10 $ do
      Ident "Par1" <- lexP 
      Par1 <$> step f
{-
      Punc "{" <- lexP 
      field <- readField "unPar1" (step f)
      Punc "}" <- lexP
      pure $ Par1 field
-}

-- move to @some@

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

-- move to @base@ or @base-orphans@

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
