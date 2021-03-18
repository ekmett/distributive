{-# Language PatternSynonyms #-}
{-# Language Trustworthy #-}
-- |
-- Copyright   : (C) 2011-2021 Edward Kmett,
--               (c) 2017-2021 Aaron Vargo,
--               (c) 2021 Oleg Grenrus
-- License     : BSD-style (see the file LICENSE)
-- Maintainer  : Edward Kmett <ekmett@gmail.com>
-- Stability   : provisional
-- Portability : non-portable (ghc 8.0+)
--
-- Examples:
--
-- For most data types you can use @GHC.Generics@ and @DeriveAnyClass@
-- along with the `Dist` newtype to fill in a ton of instances.
--
-- @
-- data V3 a = V3 a a a
--   deriving stock (Eq, Ord, Functor, Foldable, Traversable, Generic, Generic1, Data)
--   deriving anyclass Distributive
--   deriving
--   ( Applicative, Monad, MonadFix, MonadZip
--   , MonadReader (Logarithm V3)
--   , FunctorWithIndex (Logarithm V3)
--   , FoldableWithIndex (Logarithm V3)
--   , TraversableWithIndex (Logarithm V3)
--   , Eq1, Ord1
--   ) via Dist V3
--   deriving (Num, Fractional, Floating) via Dist V3 a
-- @
--
-- If you want a special form for the 'Log' of your functor you can
-- implement tabulate and index directly, `Dist` can still be used.
module Data.Distributive
( Distributive(..)
, distribute
, distrib
, dist
, collect
, cotraverse
, pattern Tabulate
-- * Default definitions
-- ** via Generics
, tabulateRep
, indexRep
, scatterRep
-- ** Simple Scattering
, scatterDefault
-- ** Canonical 'Logarithm's
, Logarithm(..)
, tabulateLogarithm
, indexLogarithm
, _logarithm
, logFromLogarithm
, logToLogarithm
, _log
, eqLog
, neLog
, gtLog
, geLog
, ltLog
, leLog
, compareLog
-- ** via DerivingVia
, Dist(..)
-- ** for other classes
-- *** Functor
, fmapDist
-- *** Applicative
, pureDist
, apDist
, liftD2
, liftD3
, liftD4
, liftD5
-- *** Monad
, bindDist
-- *** MonadFix
, mfixDist
-- *** MonadZip
, mzipWithDist
-- *** MonadReader
, askDist
, localDist
-- *** Comonad
, extractDist, extractDistBy
, extendDist, extendDistBy
, duplicateDist, duplicateDistBy
-- *** ComonadTrace
, traceDist
-- *** FunctorWithIndex
, imapDist
-- *** FoldableWithIndex
, ifoldMapDist
-- *** TraversableWithIndex
, itraverseDist
-- * Eq/Eq1
, eqDist
, neDist
, liftEqDist
-- * Ord/Ord1
, compareDist
, liftCompareDist
-- *** As right adjoints
, leftAdjunctDist
, rightAdjunctDist
) where

import Data.Distributive.Internal
