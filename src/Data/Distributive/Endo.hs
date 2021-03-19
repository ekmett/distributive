{-# Language Safe #-}

-- |
-- Copyright   : (C) 2021 Edward Kmett
-- License     : BSD-2-Clause OR Apache-2.0
-- Maintainer  : Edward Kmett <ekmett@gmail.com>
-- Stability   : provisional
-- Portability : non-portable (ghc 8.6+)
--
-- Tabulated endomorphisms
--
module Data.Distributive.Endo 
( Endo(.., Endo, appEndo)
) where

import Data.Distributive

-- | Tabulated endomorphisms.
--
-- Many representable functors can be used to memoize functions.
type role Endo nominal
newtype Endo f = EndoDist { runEndoDist :: f (Log f) }

pattern Endo :: Distributive f => (Log f -> Log f) -> Endo f
pattern Endo { appEndo } = EndoDist (Tabulate appEndo)

{-# complete Endo :: Endo #-}

instance Distributive f => Semigroup (Endo f) where
  (<>) = \f g -> Endo (appEndo f . appEndo g)
  {-# inline (<>) #-}

instance Distributive f => Monoid (Endo f) where
  mempty = EndoDist askDist
  {-# inline mempty #-}

--instance (Distributive f, Traversable f) => Eq (Endo f) where
--  (==) = liftEqDist (on (==) logToLogarithm)
