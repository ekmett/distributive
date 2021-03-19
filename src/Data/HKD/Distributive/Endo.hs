{-# Language CPP #-}
{-# Language Safe #-}
{-# Language PatternSynonyms #-}
{-# Language TypeOperators #-}
{-# Language RankNTypes #-}
-- |
-- Copyright   : (C) 2021 Edward Kmett
-- License     : BSD-2-Style OR Apache-2.0
-- Maintainer  : Edward Kmett <ekmett@gmail.com>
-- Stability   : provisional
-- Portability : non-portable (ghc 8.6+)
--
-- Tabulated endomorphisms
module Data.HKD.Distributive.Endo 
( FEndo(.., FEndo, appFEndo)
) where

import Data.HKD
import Data.HKD.Distributive

-- | Tabulated endomorphisms.
--
-- Many representable functors can be used to memoize functions.
newtype FEndo f = FEndoDist { runFEndoDist :: f (FLog f) }

pattern FEndo :: FDistributive f => (FLog f ~> FLog f) -> FEndo f
pattern FEndo { appFEndo } = FEndoDist (FTabulate appFEndo)

{-# complete FEndo #-}

instance FDistributive f => Semigroup (FEndo f) where
  (<>) = \ f g -> FEndo (appFEndo f . appFEndo g)
  {-# inline (<>) #-}

instance FDistributive f => Monoid (FEndo f) where
  mempty = FEndoDist faskFDist
  {-# inline mempty #-}

