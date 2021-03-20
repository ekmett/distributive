{-# Language AllowAmbiguousTypes #-}
{-# Language ConstraintKinds #-}
{-# Language DataKinds #-}
{-# Language PolyKinds #-}
{-# Language DerivingStrategies #-}
{-# Language GADTs #-}
{-# Language KindSignatures #-}
{-# Language MagicHash #-}
{-# Language PatternSynonyms #-}
{-# Language RankNTypes #-}
{-# Language RoleAnnotations #-}
{-# Language ScopedTypeVariables #-}
{-# Language TypeApplications #-}
{-# Language TypeOperators #-}
{-# Language Unsafe #-}
{-# Language ViewPatterns #-}
{-# options_haddock hide #-}

-- |
-- Copyright   : (C) 2021 Edward Kmett,
-- License     : BSD-2-Clause OR Apache-2.0
-- Maintainer  : Edward Kmett <ekmett@gmail.com>
-- Stability   : provisional
-- Portability : non-portable

module Numeric.Fin.Internal
( Fin(UnsafeFin,Fin,FinZ,FinS,fromFin)
, pattern IntFin
, toFin
, int
, S
, cataFin
, universe
, mirrorFin
, absurdFin
, boringFin
, isMin
, weakenRight1
, weakenLeft1
, weakenRight
, weakenLeft
, split
, append
) where

import Control.Monad
import Data.Coerce
import Data.GADT.Show
import Data.Type.Equality
import GHC.Exts
import GHC.Ix
import GHC.TypeNats
import Text.Read
import Unsafe.Coerce

-- | Turn a KnownNat into an Int. Use with @TypeApplications@.
--
-- >>> int @5
-- 5
int :: forall n. KnownNat n => Int
int = fromIntegral $ natVal' (proxy# @n)

-- | The successor of a natural number.
type S n = 1 + n

-- | @'Fin' n@ is a natural number < @n@.
-- In practice, we limit ourselves by encoding it as an 'Int'
-- as it unboxes better, and most of the time you take it out
-- you are immediately going to convert it to such. If you really
-- need a bigger a 'Fin', you'll need to roll your own.
type role Fin nominal
newtype Fin (n :: Nat)
  -- | This is more unsafe than it looks.
  = UnsafeFin
  { fromFin :: Int
  }
  deriving stock (Eq, Ord, Ix)

type a /~ b = (a == b) ~ 'False

instance (0 /~ n, KnownNat n) => Bounded (Fin n) where
  minBound = UnsafeFin 0
  maxBound = UnsafeFin (int @n - 1)
  {-# inline minBound #-}
  {-# inline maxBound #-}

instance (0 /~ n, KnownNat n) => Enum (Fin n) where
  succ (Fin i)
    | i < int @n - 1 = UnsafeFin (i + 1)
    | otherwise = error "Fin.succ: too big"
  pred (Fin 0) = error "Fin.pred: too small"
  pred (Fin n) = UnsafeFin (n - 1)
  fromEnum = fromFin
  toEnum x
    | x < 0 = error "Fin.toEnum: negative"
    | otherwise = UnsafeFin x
  enumFrom = coerce $ enumFrom @Int
  enumFromTo = coerce (enumFromTo @Int)
  enumFromThen (Fin i) (Fin j)
    | i <= j = coerce $ enumFromThenTo i j (int @n)
    | otherwise = coerce $ enumFromThenTo i j 0
  enumFromThenTo = coerce (enumFromThenTo @Int)

instance GShow Fin where
  gshowsPrec = showsPrec
  {-# inline gshowsPrec #-}

instance Show (Fin n) where
  showsPrec = coerce (showsPrec :: Int -> Int -> String -> String)
  {-# inline showsPrec #-}

instance KnownNat n => Read (Fin n) where
  readPrec = do
    i <- readPrec
    UnsafeFin i <$ guard (i < int @n)
  {-# inline readPrec #-}

-- | You can pattern match on a Fin with this constructor,
-- but not construct. If you really truly want need to
-- construct a 'Fin' using an unsafe naked 'Int' and you
-- pinky-swear that you are going to do it correctly,
-- look at 'UnsafeFin', you animal.
--
-- >>> Fin (FinS FinZ)
-- 1
pattern Fin :: Int -> Fin n
pattern Fin n <- UnsafeFin n
{-# complete Fin #-}

-- | You can construct a Fin safely this way.
--
-- >>> toFin 2 :: Fin 4
-- Just 2
--
-- >>> toFin 2 :: Fin 2
-- Nothing
toFin :: forall n. KnownNat n => Int -> Maybe (Fin n)
toFin i
  | 0 <= i && i < int @n = Just (UnsafeFin i)
  | otherwise  = Nothing
{-# inline toFin #-}

-- | This is a pattern on 'Int' that can be used to
-- safely construct a Fin. Pattern match fails
-- if the 'Int' of out of bounds.
--
-- >>> case 3 of IntFin (n :: Fin 5) -> "good"; _ -> "bad"
-- "good"
--
-- >>> case 3 of IntFin (n :: Fin 3) -> "good"; _ -> "bad"
-- "bad"
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

-- | A safe pattern for matching 0. A safe, useful basecase.
pattern FinZ :: () => forall m. (n ~ S m) => Fin n
pattern FinZ <- (upFin -> FinZ') where
  FinZ = UnsafeFin 0

-- | A safe pattern for matching on the successor. Useful for induction.
pattern FinS :: () => forall m. (n ~ S m) => Fin m -> Fin n
pattern FinS n <- (upFin -> FinS' n) where
  FinS n = UnsafeFin (fromFin n - 1)

{-# complete FinZ, FinS :: Fin #-}

universe :: forall n. KnownNat n => [Fin n]
universe = UnsafeFin <$> [0 .. int @n - 1]

-- | @'Fin' 0@ is uninhabited
absurdFin :: Fin 0 -> a
absurdFin (Fin _) = error "absurdFin: inhabited Fin 0"
{-# inline absurdFin #-}

cataFin :: forall a n. (a -> a) -> a -> Fin n -> a
cataFin f z = coerce go where
  go :: Int -> a
  go 0 = z
  go k = f $ go $ k-1
{-# inline cataFin #-}

boringFin :: Fin 1
boringFin = FinZ
{-# inline boringFin #-}

-- | Return one less.
--
-- >>> isMin (FZ :: Fin 1)
-- Nothing
--
-- >>> map isMin [minBound..maxBound] :: [Maybe (Fin 3)]
-- [Nothing,Just 0,Just 1,Just 2]
--
-- @since 0.1.1
isMin :: Fin (1 + n) -> Maybe (Fin n)
isMin (Fin 0) = Nothing
isMin (Fin n) = Just $ UnsafeFin $ n - 1
{-# inline isMin #-}

-- | >>> map weakenRight1 universe :: [Fin 5]
-- [1,2,3,4]
--
-- @since 0.1.1
weakenRight1 :: Fin n -> Fin (S n)
weakenRight1 = FinS
{-# inline weakenRight1 #-}

-- | >>> map weakenLeft1 universe :: [Fin 5]
-- [0,1,2,3]
weakenLeft1 :: Fin n -> Fin (S n)
weakenLeft1 (Fin n) = UnsafeFin n
{-# inline weakenLeft1 #-}

-- | >>> map (weakenRight @2) (universe :: [Fin 3])
-- [2,3,4]
weakenRight :: forall n m. KnownNat n => Fin m -> Fin (n + m)
weakenRight (Fin m) = UnsafeFin $ int @n + m
{-# inline weakenRight #-}

-- | >>> map (weakenLeft @2) (universe :: [Fin 3])
-- [0,1,2]
weakenLeft :: forall m n. Fin n -> Fin (n + m)
weakenLeft (Fin n) = UnsafeFin n
{-# inline weakenLeft #-}

-- | Append two 'Fin's together.
--
-- >>> append (Left fin2 :: Either (Fin N.Nat5) (Fin N.Nat4))
-- 2
--
-- >>> append (Right fin2 :: Either (Fin N.Nat5) (Fin N.Nat4))
-- 7
append :: forall n m. KnownNat n => Either (Fin n) (Fin m) -> Fin (n + m)
append (Left n)  = weakenLeft @m n
append (Right m) = weakenRight @n m
{-# inline append #-}

-- | Inverse of 'append'.
--
-- >>> split fin2 :: Either (Fin 2) (Fin 3)
-- Right 0
--
-- >>> split fin1 :: Either (Fin 2) (Fin 3)
-- Left 1
--
-- >>> map split universe :: [Either (Fin N.Nat2) (Fin N.Nat3)]
-- [Left 0,Left 1,Right 0,Right 1,Right 2]
--
split :: forall n m. KnownNat n => Fin (n + m) -> Either (Fin n) (Fin m)
split (Fin i)
  | i < n     = Left (UnsafeFin i)
  | otherwise = Right (UnsafeFin $ i - n)
  where n = int @n
{-# inline split #-}

mirrorFin :: forall n. KnownNat n => Fin n -> Fin n
mirrorFin (Fin i) = UnsafeFin (int @n - i - 1)
{-# inline mirrorFin #-}
