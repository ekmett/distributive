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
--   deriving anyclass Representable
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
module Data.Functor.Rep
( Indexable(..)
, Representable(..)
, dist
, distrib
, distribute
, distributeLim
, distributeForall
, collect
, cotraverse
, pattern Tabulate
-- * Default definitions
-- ** via Generics
, indexGeneric
, scatterGeneric
, tabulateGeneric
-- ** via index/tabulate
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
, fmapRep
-- *** Applicative
, pureRep
, apRep
, liftR2
, liftR3
, liftR4
, liftR5
-- *** Monad
, bindRep
-- *** MonadFix
, mfixRep
-- *** MonadZip
, mzipWithRep
-- *** MonadReader
, askRep
, localRep
-- *** Comonad
, extractRep, extractRepBy
, extendRep, extendRepBy
, duplicateRep, duplicateRepBy
-- *** ComonadTrace
, traceRep
-- *** FunctorWithIndex
, imapRep
-- *** FoldableWithIndex
, ifoldMapRep
-- *** TraversableWithIndex
, itraverseRep
-- * Eq/Eq1
, eqRep
, neRep
, liftEqRep
-- * Ord/Ord1
, compareRep
, liftCompareRep
-- *** As right adjoints
, leftAdjunctRep
, rightAdjunctRep
) where

import Data.Functor.Rep.Internal
import Data.Fin.Internal
