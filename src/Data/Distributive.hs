{-# Language PatternSynonyms #-}
{-# Language Trustworthy #-}
-- |
-- Copyright   : (C) 2011-2021 Edward Kmett,
--               (c) 2017-2021 Aaron Vargo,
--               (c) 2021 Oleg Grenrus
-- License     : BSD-2-Clause OR Apache-2.0
-- Maintainer  : Edward Kmett <ekmett@gmail.com>
-- Stability   : provisional
-- Portability : non-portable
--
-- For most distributive data types you can use @GHC.Generics@ and @DeriveAnyClass@
-- along with the `Dist` newtype to fill in a ton of instances.
--
-- @
-- data V3 a = V3 a a a
--   deriving stock 
--   ( Show, Read, Eq, Ord
--   , Functor, Foldable, Traversable
--   , Generic, Generic1, Data )
--   deriving anyclass Distributive
--   deriving
--   ( Applicative, Monad, MonadFix, MonadZip
--   , MonadReader (Fin 3)
--   , FunctorWithIndex (Fin 3)
--   , FoldableWithIndex (Fin 3)
--   , TraversableWithIndex (Fin 3)
--   , Eq1, Ord1 )                        via Dist V3
--   deriving (Num, Fractional, Floating) via Dist V3 a
-- @
--
-- If you want a special form for the 'Log' of your functor you can
-- implement tabulate and index directly and `Dist` can still be used.
--
-- See 'Data.Machine.Moore' for an example of this pattern.
module Data.Distributive
( Indexable(..)
, Distributive(..)
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
, Fin(Fin,FinZ,FinS,fromFin)
, pattern IntFin
, toFin
, absurdFin
, indexFin
, tabulateFin
-- * Generically deriving indexing by Fin
, DefaultTabulateFin
, gtabulateFin
, DefaultIndexFin
, gindexFin
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
import Data.Distributive.Internal.Fin
