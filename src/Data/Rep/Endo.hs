{-# Language Safe #-}

-- |
-- Copyright   : (C) 2021 Edward Kmett
-- License     : BSD-2-Clause OR Apache-2.0
-- Maintainer  : Edward Kmett <ekmett@gmail.com>
-- Stability   : provisional
-- Portability : non-portable
--
-- Tabulated endomorphisms
--
module Data.Rep.Endo 
( Endo(.., Endo, appEndo)
) where

import Data.Rep

-- | Tabulated endomorphisms.
--
-- Many representable functors can be used to memoize functions.
type role Endo nominal
newtype Endo f = EndoDist { runEndoDist :: f (Log f) }

pattern Endo :: Representable f => (Log f -> Log f) -> Endo f
pattern Endo { appEndo } = EndoDist (Tabulate appEndo)

{-# complete Endo :: Endo #-}

instance Representable f => Semigroup (Endo f) where
  (<>) = \f g -> Endo (appEndo f . appEndo g)
  {-# inline (<>) #-}

instance Representable f => Monoid (Endo f) where
  mempty = EndoDist askRep
  {-# inline mempty #-}

--instance (Representable f, Traversable f) => Eq (Endo f) where
--  (==) = liftEqDist (on (==) logToLogarithm)
