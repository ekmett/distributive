{-# Language GADTs #-}
{-# Language PatternSynonyms #-}
{-# Language RoleAnnotations #-}
{-# Language ViewPatterns #-}
{-# Language RankNTypes #-}
{-# Language KindSignatures #-}
{-# Language DerivingStrategies #-}
{-# Language GeneralizedNewtypeDeriving #-}
{-# Language DataKinds #-}
{-# Language PolyKinds #-}
{-# Language TypeOperators #-}
{-# Language ScopedTypeVariables #-}
{-# Language Unsafe #-}
{-# Language TypeFamilies #-}
{-# Language UndecidableInstances #-}
{-# Language FlexibleContexts #-}

module Data.HKD.Distributive.Internal.Fin 
( FFin(FUnsafeFin,FFin,FFinZ,FFinS)
, lowerFin, liftFin
, pattern IntFFin
, toFFin
) where

import Control.Arrow (first)
import Data.Coerce
import Data.Distributive.Internal.Fin
import Data.GADT.Compare
import Data.GADT.Show
import Data.Kind
import Data.Some
import Data.Type.Coercion
import Data.Type.Equality
import GHC.TypeLits
import Unsafe.Coerce

type role FFin nominal nominal 

type family Length (as ::[i]) :: Nat where
  Length '[] = 0
  Length (x ': xs) = 1 + Length xs

newtype FFin (as :: [i]) (a :: i) = FUnsafeFin { fromFFin :: Int }
  deriving newtype (Eq, Ord, Show)

pattern FFin :: Int -> FFin as i
pattern FFin i <- FUnsafeFin i

{-# complete FFin #-}

type role FFin' nominal nominal 
data FFin' :: [i] -> i -> Type where
  FFinZ' :: FFin' (a:as) a
  FFinS' :: FFin as a -> FFin' (b:as) a

liftFin :: forall i (as :: [i]). Fin (Length as) -> Some (FFin as)
liftFin = \(Fin i) -> Some (FUnsafeFin i)
{-# inline liftFin #-}

lowerFin :: forall i (as :: [i]) (a :: i). FFin as a -> Fin (Length as)
lowerFin = coerce
{-# inline lowerFin #-}

pattern IntFFin
  :: forall i (as :: [i]). KnownNat (Length as) => forall (a :: i). FFin as a -> Int
pattern IntFFin i <- (toFFin -> Just (Some i)) where
  IntFFin i = fromFFin i

toFFin :: KnownNat (Length is) => Int -> Maybe (Some (FFin is))
toFFin = fmap liftFin . toFin
{-# inline toFFin #-}

upFFin :: FFin is i -> FFin' is i
upFFin (FFin 0) = unsafeCoerce FFinZ'
upFFin (FFin n) = unsafeCoerce $ FFinS' $ FUnsafeFin (n - 1)
{-# inline upFFin #-}

pattern FFinZ :: () => forall bs. as ~ (a:bs) => FFin as a 
pattern FFinZ <- (upFFin -> FFinZ') where
  FFinZ = FUnsafeFin 0

pattern FFinS :: () => forall bs. as ~ (b:bs) => FFin bs a -> FFin as a
pattern FFinS n <- (upFFin -> FFinS' n) where
  FFinS n = FUnsafeFin (fromFFin n + 1)

{-# complete FFinZ, FFinS #-}

instance GEq (FFin is) where
  geq = \(FFin i) (FFin j) ->
    if i == j 
    then Just (unsafeCoerce Refl)
    else Nothing
  {-# inline geq #-}

instance GCompare (FFin is) where
  gcompare = \(FFin i) (FFin j) ->
    case compare i j of
      LT -> GLT
      EQ -> unsafeCoerce GEQ
      GT -> GGT
  {-# inline gcompare #-}

instance TestEquality (FFin is) where
  testEquality = geq
  {-# inline testEquality #-}

instance TestCoercion (FFin is) where
  testCoercion x y = repr <$> geq x y
  {-# inline testCoercion #-}

instance GShow (FFin as) where
  gshowsPrec = showsPrec
  {-# inline gshowsPrec #-}

instance KnownNat (Length as) => GRead (FFin as) where
  greadsPrec = \ d s -> first (liftFinWith mkGReadResult) <$> readsPrec d s

liftFinWith :: forall i (as :: [i]) f. (forall (x :: i -> Type) (a :: i). x a -> f x) -> Fin (Length as) -> f (FFin as)
liftFinWith = \ f (Fin i) -> f (FUnsafeFin i)
{-# inline liftFinWith #-}

