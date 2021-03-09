{-# LANGUAGE CPP #-}
-- |
-- Copyright   : (C) 2021 Edward Kmett
-- License     : BSD-style (see the file LICENSE)
--
-- Maintainer  : Edward Kmett <ekmett@gmail.com>
-- Stability   : provisional
-- Portability : non-portable (ghc 8.0+)
--
-- Tabulated endomorphisms
module Data.Distributive.Endo 
  (
    DistEndo(..)
  , tabulateDistEndo
  , indexDistEndo
  ) where

import Data.Distributive
import Data.Distributive.Util

#if __GLASGOW_HASKELL__ < 804
import Data.Semigroup (Semigroup(..))
#endif

-- | Tabulated endomorphisms.
--
-- Many representable functors can be used to memoize functions.
newtype DistEndo f = DistEndo { runDistEndo :: f (Log f) }

instance Distributive f => Semigroup (DistEndo f) where
  DistEndo f <> DistEndo g = DistEndo $ tabulate $ \x -> index f (index g x)
  {-# inline (<>) #-}

instance Distributive f => Monoid (DistEndo f) where
#if __GLASGOW_HASKELL__ < 804
  DistEndo f `mappend` DistEndo g = DistEndo $ tabulate $ \x -> index f (index g x)
  {-# inline mappend #-}
#endif
  mempty = DistEndo askDist
  {-# inline mempty #-}

indexDistEndo :: Distributive f => DistEndo f -> Log f -> Log f
indexDistEndo = index .# runDistEndo
{-# inline indexDistEndo #-}

tabulateDistEndo :: Distributive f => (Log f -> Log f) -> DistEndo f
tabulateDistEndo = DistEndo #. tabulate
{-# inline tabulateDistEndo #-}

