{-# Language Trustworthy #-}

-- |
-- Copyright   :  (C) 2012-2021 Edward Kmett
-- License     :  BSD-2-Style OR Apache-2.0
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  non-portable
--
-- <http://en.wikipedia.org/wiki/Mealy_machine>

module Data.Machine.Mealy
( Mealy(..)
, logMealy
, unfoldMealy
, driveMealy
) where

import Control.Applicative
import Control.Arrow
import Control.Category
import Control.Monad.Fix
import Control.Monad.Zip
import Control.Monad.Reader.Class
import Data.Functor.WithIndex
import Data.Machine.Moore
import Data.Sequence (Seq(..), ViewL(..), viewl)
import Data.List.NonEmpty
import Data.Rep
import GHC.Generics
import Numeric
import Prelude hiding (id,(.))
-- @Data.Sequence@ is merely safe-inferred, so we get complained at if we claim to be @Safe@ but we also
-- get complained at if we claim to be @Trustworthy@. @import Trustworthy ()@ downgrades us cleanly
-- to @Trustworthy@ without complaint. Did I mention that I find the design of SafeHaskell to be
-- nearly unusable at present? If you are wondering why this module has to be included your trusted
-- code base, this is why.
import Trustworthy ()

type role Mealy representational nominal
data Mealy a b = Mealy { runMealy :: a -> Moore a b }
  deriving stock (Functor, Generic, Generic1)
  deriving
  ( Applicative, Monad, MonadFix, MonadZip
  , MonadReader (NonEmpty a)
  , FunctorWithIndex (NonEmpty a)
  ) via Dist (Mealy a)
  deriving
  ( Semigroup, Monoid, Num, Fractional, Floating
  )  via Dist (Mealy a) b

instance Category Mealy where
  id = Mealy go where
    go a = Moore a go
  {-# inline id #-}

  (.) = \(Mealy bc0) (Mealy ab0) -> Mealy (go bc0 ab0) where
    go bc ab a = case ab a of
      Moore b nab -> case bc b of
        Moore c nbc -> Moore c (go nbc nab)
  {-# inline (.) #-}

instance Arrow Mealy where
  arr f = Mealy go where
    go a = Moore (f a) go
  {-# inline arr #-}

  first = \(Mealy m0) -> Mealy (go m0) where
    go m (a,c) = case m a of
      Moore b n -> Moore (b, c) (go n)
  {-# inline first #-}

  second = \(Mealy m0) -> Mealy (go m0) where
    go m (c,a) = case m a of
      Moore b n -> Moore (c, b) (go n)
  {-# inline second #-}

  (***) = \(Mealy x0) (Mealy y0) -> Mealy (go x0 y0) where
    go x y (a,b) = case x a of
      Moore xa nxa -> case y b of
        Moore yb nyb -> Moore (xa, yb) (go nxa nyb)
  {-# inline (***) #-}

  (&&&) = \(Mealy x0) (Mealy y0) -> Mealy (go x0 y0) where
    go x y a = case x a of
      Moore xa nxa -> case y a of
        Moore yb nya -> Moore (xa, yb) (go nxa nya)
  {-# inline (&&&) #-}

instance ArrowChoice Mealy where
  left = \(Mealy m0) -> Mealy $ go m0 where
    go m = \case
      Left l -> case m l of
        Moore b m' -> Moore (Left b) (go m')
      Right r -> Moore (Right r) (go m)
  {-# inline left #-}
  right = \(Mealy m0) -> Mealy $ go m0 where
    go m = \case
      Left l -> Moore (Left l) (go m)
      Right r -> case m r of
        Moore b m' -> Moore (Right b) (go m')
  {-# inline right #-}
  (+++) = \(Mealy m0) (Mealy n0) -> Mealy $ go m0 n0 where
    go m n = \case
      Left b -> case m b of
        Moore c m' -> Moore (Left c) (go m' n)
      Right b -> case n b of
        Moore c n' -> Moore (Right c) (go m n')
  {-# inline (+++) #-}
  (|||) = \(Mealy m0) (Mealy n0) -> Mealy $ go m0 n0 where
    go m n = \case
      Left b -> case m b of
        Moore d m' -> Moore d (go m' n)
      Right b -> case n b of
        Moore d n' -> Moore d (go m n')
  {-# inline (|||) #-}

instance Indexable (Mealy a) where
  type Log (Mealy a) = NonEmpty a
  index = \(Mealy f) (x:|xs) -> index (f x) xs
  {-# inline index #-}

instance Representable (Mealy a) where
  tabulate = \f -> Mealy $ \a -> tabulate (f . (a :|))
  {-# inline tabulate #-}

-- | A 'Mealy' machine modeled with explicit state.
unfoldMealy :: (s -> a -> (b, s)) -> s -> Mealy a b
unfoldMealy f = go where
  go s = Mealy $ \a -> case f s a of
    (b, t) -> Moore b (runMealy $ go t)
{-# inline unfoldMealy #-}

logMealy :: Semigroup a => Mealy a a
logMealy = Mealy $ \a -> Moore a (h a) where
  h a = \((a <>) -> b) -> Moore b (h b)
{-# inline logMealy #-}

-- | Fast forward a mealy machine forward
driveMealy :: Mealy a b -> Seq a -> Mealy a b
driveMealy m xs = case viewl xs of
  y :< ys -> case runMealy m y of
    Moore _ n -> driveMealy (Mealy n) ys
  EmptyL -> m
