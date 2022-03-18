{-# Language CPP #-}
{-# Language DerivingVia #-}
{-# Language Trustworthy #-}

-- |
-- Copyright   :  (C) 2012-2021 Edward Kmett
-- License     :  BSD-2-Style OR Apache-2.0
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  non-portable
--
-- <http://en.wikipedia.org/wiki/Moore_machine>

module Data.Machine.Moore
( Moore(..)
, logMoore
, unfoldMoore
) where

import Control.Applicative
#ifdef MIN_VERSION_comonad
import Control.Comonad
#endif
import Control.Monad.Fix
import Control.Monad.Zip
import Control.Monad.Reader.Class
import Data.Rep
import Data.Coerce
import Data.Profunctor.Closed
import Data.Profunctor.Unsafe
import Data.Profunctor.Strong
import Data.Profunctor.Sieve
import qualified Data.Profunctor.Rep as Pro
import Data.Functor.WithIndex
import GHC.Generics
import Numeric
import Prelude

type role Moore representational representational
data Moore a b = Moore b (a -> Moore a b)
  deriving stock (Functor, Generic, Generic1)
  deriving
  ( Applicative, Monad, MonadFix, MonadZip, MonadReader [a], FunctorWithIndex [a]
#ifdef MIN_VERSION_comonad
  , Comonad, ComonadApply
#endif
  ) via Dist (Moore a)
  deriving (Semigroup, Monoid, Num, Fractional, Floating)  via Dist (Moore a) b

instance Indexable (Moore a) where
  type Log (Moore a) = [a]
  index = \(Moore b k) -> \case
    [] -> b
    (a:as) -> index (k a) as
  {-# inline index #-}

instance Representable (Moore a) where
  tabulate = \f -> Moore (f []) \a -> tabulate (f.(a:))
  {-# inline tabulate #-}

-- | Accumulate the input as a sequence.
logMoore :: Monoid m => Moore m m
logMoore = h mempty where
  h m = Moore m \a -> h (m <> a)
{-# inline logMoore #-}

-- | Construct a Moore machine from a state valuation and transition function
unfoldMoore :: (s -> b) -> (s -> a -> s) -> s -> Moore a b
unfoldMoore = \f g s -> Moore (f s) (unfoldMoore f g . g s)
{-# inline unfoldMoore #-}

instance Profunctor Moore where
  rmap = fmap
  {-# INLINE rmap #-}
  lmap f = go where
    go (Moore b g) = Moore b (go . g . f)
  {-# INLINE lmap #-}
  dimap f g = go where
    go (Moore b h) = Moore (g b) (go . h . f)
  {-# INLINE dimap #-}
  (#.) _ = coerce
  {-# INLINE (#.) #-}
  (.#) g _ = coerce g
  {-# INLINE (.#) #-}

instance Cosieve Moore [] where
  cosieve (Moore b k) = \case
    [] -> b
    (a:as) -> cosieve (k a) as
  {-# INLINE cosieve #-}

instance Costrong Moore where
  unfirst = Pro.unfirstCorep
  unsecond = Pro.unsecondCorep
  {-# INLINE unfirst #-}
  {-# INLINE unsecond #-}

instance Pro.Corepresentable Moore where
  type Corep Moore = []
  cotabulate = \f -> Moore (f []) \a -> Pro.cotabulate (f.(a:))
  {-# INLINE cotabulate #-}

instance Closed Moore where
  closed = \m -> Pro.cotabulate \fs x -> cosieve m (fmap ($x) fs)
  {-# INLINE closed #-}
