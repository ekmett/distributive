{-# Language AllowAmbiguousTypes #-}
{-# Language DataKinds #-}
{-# Language DerivingVia #-}
{-# Language GADTs #-}
{-# Language MagicHash #-}
{-# Language MultiParamTypeClasses #-}
{-# Language PatternSynonyms #-}
{-# Language PolyKinds #-}
{-# Language RankNTypes #-}
{-# Language RoleAnnotations #-}
{-# Language ScopedTypeVariables #-}
{-# Language TypeApplications #-}
{-# Language TypeFamilies #-}
{-# Language TypeOperators #-}
{-# Language UnboxedTuples #-}
{-# Language Unsafe #-}
{-# Language ViewPatterns #-}
{-# options_haddock hide #-}

module Data.Distributive.Internal.Fin
( Fin(UnsafeFin,Fin,FinZ,FinS)
, pattern IntFin
, toFin
, int
, S
) where

import Control.Monad
import Data.Distributive.Internal.Coerce
import Data.GADT.Compare
import Data.GADT.Show
import Data.Type.Coercion
import Data.Type.Equality
import GHC.Exts
import GHC.TypeNats
import Text.Read
import Unsafe.Coerce

int :: forall n. KnownNat n => Int
int = fromIntegral $ natVal' (proxy# @n)

type S n = 1 + n

type role Fin nominal
newtype Fin (n :: Nat) = UnsafeFin { fromFin :: Int }
  deriving (Eq, Ord)

instance GShow Fin where
  gshowsPrec = showsPrec

instance Show (Fin n) where
  showsPrec = \d -> showsPrec d .# fromFin

instance KnownNat n => Read (Fin n) where
  readPrec = do
    i <- readPrec
    UnsafeFin i <$ guard (i < int @n)

instance GEq Fin where
  geq = \(UnsafeFin x) (UnsafeFin y) ->
    if x == y 
    then Just (unsafeCoerce Refl)
    else Nothing
  {-# inline geq #-}

instance GCompare Fin where
  gcompare = \(UnsafeFin x) (UnsafeFin y) -> case compare x y of
    LT -> GLT
    EQ -> unsafeCoerce GEQ
    GT -> GGT
  {-# inline gcompare #-}

instance TestEquality Fin where
  testEquality = geq
  {-# inline testEquality #-}

instance TestCoercion Fin where
  testCoercion = \a b -> repr <$> geq a b
  {-# inline testCoercion #-}

pattern Fin :: Int -> Fin n
pattern Fin n <- UnsafeFin n
{-# complete Fin #-}

toFin :: forall n. KnownNat n => Int -> Maybe (Fin n)
toFin i
  | i < int @n = Just (UnsafeFin i)
  | otherwise  = Nothing
{-# inline toFin #-}

pattern IntFin :: KnownNat n => Fin n -> Int
pattern IntFin i <- (toFin -> Just i) where
  IntFin x = fromFin x

data Fin' (n :: Nat) where
  FinZ' :: Fin' (S n)
  FinS' :: Fin n -> Fin' (S n)

upFin :: Fin n -> Fin' n
upFin (UnsafeFin 0) = unsafeCoerce FinZ'
upFin (UnsafeFin n) = unsafeCoerce $ FinS' $ UnsafeFin (n-1)
{-# inline[0] upFin #-}

pattern FinZ :: () => forall m. (n ~ S m) => Fin n
pattern FinZ <- (upFin -> FinZ') where
  FinZ = UnsafeFin 0

pattern FinS :: () => forall m. (n ~ S m) => Fin m -> Fin n
pattern FinS n <- (upFin -> FinS' n) where
  FinS n = UnsafeFin (fromFin n - 1)

{-# complete FinZ, FinS :: Fin #-}
