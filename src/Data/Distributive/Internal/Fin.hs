{-# Language UnboxedTuples #-}
{-# Language Unsafe #-}
{-# options_haddock hide #-}

-- |
-- Copyright   : (C) 2021 Edward Kmett,
-- License     : BSD-2-Clause OR Apache-2.0
-- Maintainer  : Edward Kmett <ekmett@gmail.com>
-- Stability   : provisional
-- Portability : non-portable

module Data.Distributive.Internal.Fin
( Fin(UnsafeFin,Fin,FinZ,FinS,fromFin)
, pattern IntFin
, toFin
, int
, S
, absurdFin
) where

import Control.Monad
import Data.GADT.Show
import GHC.Exts
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
  deriving stock (Eq, Ord)

instance GShow Fin where
  gshowsPrec = showsPrec

instance Show (Fin n) where
  showsPrec = coerce (showsPrec :: Int -> Int -> String -> String)

instance KnownNat n => Read (Fin n) where
  readPrec = do
    i <- readPrec
    UnsafeFin i <$ guard (i < int @n)

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

-- | Fin 0 is uninhabited
absurdFin :: Fin 0 -> a
absurdFin (Fin _) = error "absurdFin: inhabited Fin 0"
{-# inline absurdFin #-}
