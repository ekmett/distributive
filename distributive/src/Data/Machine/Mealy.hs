{-# Language Safe #-}

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
) where

import Control.Applicative
import Control.Monad.Fix
import Control.Monad.Zip
import Control.Monad.Reader.Class
import Data.Functor.WithIndex
import Data.Machine.Moore
import Data.List.NonEmpty
import Data.Rep
import GHC.Generics
import Numeric
import Prelude

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

instance Indexable (Mealy a) where
  type Log (Mealy a) = NonEmpty a
  index (Mealy f) (x:|xs) = index (f x) xs
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
