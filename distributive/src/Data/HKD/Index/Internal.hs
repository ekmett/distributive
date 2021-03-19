{-# Language GeneralizedNewtypeDeriving #-}
{-# Language Unsafe #-}
{-# options_haddock not-home #-}

-- |
-- Copyright   : (C) 2021 Edward Kmett,
-- License     : BSD-2-style OR Apache-2.0
-- Maintainer  : Edward Kmett <ekmett@gmail.com>
-- Stability   : provisional
-- Portability : non-portable

module Data.HKD.Index.Internal
( Index(UnsafeIndex,Index,IndexZ,IndexS)
, lowerFin, liftFin
, pattern IntIndex
, toIndex
, Length
, KnownLength
, len
) where

import Control.Arrow (first)
import Data.Coerce
import Data.GADT.Compare
import Data.GADT.Show
import Data.Kind
import Data.Some
import Data.Type.Coercion
import Data.Type.Equality
import GHC.TypeLits
import Numeric.Fin.Internal
import Unsafe.Coerce

type role Index nominal nominal

type family Length (as :: [i]) :: Nat where
  Length '[] = 0
  Length (x ': xs) = 1 + Length xs

newtype Index (as :: [i]) (a :: i) = UnsafeIndex { fromIndex :: Int }
  deriving newtype (Eq, Ord, Show)

pattern Index :: Int -> Index as i
pattern Index i <- UnsafeIndex i
{-# complete Index #-}

len :: forall as. KnownLength as => Int
len = int @(Length as)
{-# inline len #-}

liftFin :: forall i (as :: [i]). Fin (Length as) -> Some (Index as)
liftFin = \(Fin i) -> Some (UnsafeIndex i)
{-# inline liftFin #-}

lowerFin :: forall i (as :: [i]) (a :: i). Index as a -> Fin (Length as)
lowerFin = coerce
{-# inline lowerFin #-}

type role Index' nominal nominal
data Index' :: [i] -> i -> Type where
  IndexZ' :: Index' (a:as) a
  IndexS' :: Index as a -> Index' (b:as) a

type KnownLength (as :: [i]) = KnownNat (Length as)

pattern IntIndex
  :: forall i (as :: [i]). KnownLength as
  => forall (a :: i). Index as a -> Int
pattern IntIndex i <- (toIndex -> Just (Some i)) where
  IntIndex i = fromIndex i

toIndex :: KnownLength is => Int -> Maybe (Some (Index is))
toIndex = fmap liftFin . toFin
{-# inline toIndex #-}

upIndex :: Index is i -> Index' is i
upIndex (Index 0) = unsafeCoerce IndexZ'
upIndex (Index n) = unsafeCoerce $ IndexS' $ UnsafeIndex (n - 1)
{-# inline[0] upIndex #-}

pattern IndexZ :: () => forall bs. as ~ (a:bs) => Index as a
pattern IndexZ <- (upIndex -> IndexZ') where
  IndexZ = UnsafeIndex 0

pattern IndexS :: () => forall bs. as ~ (b:bs) => Index bs a -> Index as a
pattern IndexS n <- (upIndex -> IndexS' n) where
  IndexS n = UnsafeIndex (fromIndex n + 1)

{-# complete IndexZ, IndexS #-}

instance GEq (Index is) where
  geq = \(Index i) (Index j) ->
    if i == j
    then Just (unsafeCoerce Refl)
    else Nothing
  {-# inline geq #-}

instance GCompare (Index is) where
  gcompare = \(Index i) (Index j) ->
    case compare i j of
      LT -> GLT
      EQ -> unsafeCoerce GEQ
      GT -> GGT
  {-# inline gcompare #-}

instance TestEquality (Index is) where
  testEquality = geq
  {-# inline testEquality #-}

instance TestCoercion (Index is) where
  testCoercion = \x y -> repr <$> geq x y
  {-# inline testCoercion #-}

instance GShow (Index as) where
  gshowsPrec = showsPrec
  {-# inline gshowsPrec #-}

instance KnownLength as => GRead (Index as) where
  greadsPrec = \ d s -> first (liftFinWith mkGReadResult) <$> readsPrec d s

liftFinWith :: forall i (as :: [i]) f. (forall (x :: i -> Type) (a :: i). x a -> f x) -> Fin (Length as) -> f (Index as)
liftFinWith = \ f (Fin i) -> f (UnsafeIndex i)
{-# inline liftFinWith #-}

