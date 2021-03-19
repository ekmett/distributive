{-# Language Safe #-}

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
import Control.Monad.Fix
import Control.Monad.Zip
import Control.Monad.Reader.Class
import Data.Functor.Rep
import Data.Functor.WithIndex
import GHC.Generics
import Numeric
import Prelude

-- data Moore a b where
--   Moore :: Representable f => f b -> (a -> Endo f) -> Log f -> Moore a b

-- [a] -> b

data Moore a b = Moore b (a -> Moore a b)
  deriving stock (Functor, Generic, Generic1)
  deriving (Applicative, Monad, MonadFix, MonadZip, MonadReader [a], FunctorWithIndex [a]) via Dist (Moore a)
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
