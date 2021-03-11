{-# Language CPP #-}
{-# Language Safe #-}
{-# Language PatternSynonyms #-}
{-# Language ViewPatterns #-}
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
#if __GLASGOW_HASKELL__ >= 802
    Endo(.., Endo, appEndo)
#else
    Endo(.., Endo)
  , appEndo
#endif
  ) where

import Data.Distributive
#if __GLASGOW_HASKELL__ < 802
import Data.Distributive.Util
#endif

#if __GLASGOW_HASKELL__ < 804
import Data.Semigroup (Semigroup(..))
#endif

-- | Tabulated endomorphisms.
--
-- Many representable functors can be used to memoize functions.
newtype Endo f = EndoDist { runEndoDist :: f (Log f) }

pattern Endo :: Distributive f => (Log f -> Log f) -> Endo f
#if __GLASGOW_HASKELL__ >= 802
pattern Endo { appEndo } <- EndoDist (index -> appEndo) where
  Endo f = EndoDist (tabulate f)
#else
pattern Endo f <- EndoDist (index -> f) where
  Endo f = EndoDist (tabulate f)

appEndo :: Distributive f => Endo f -> Log f -> Log f
appEndo = index .# runEndoDist
{-# inline getEndo #-}
#endif

instance Distributive f => Semigroup (Endo f) where
  EndoDist f <> EndoDist g = EndoDist $ tabulate $ \x -> index f (index g x)
  {-# inline (<>) #-}

instance Distributive f => Monoid (Endo f) where
#if __GLASGOW_HASKELL__ < 804
  EndoDist f `mappend` EndoDist g = EndoDist $ tabulate $ \x -> index f (index g x)
  {-# inline mappend #-}
#endif
  mempty = EndoDist askDist
  {-# inline mempty #-}

