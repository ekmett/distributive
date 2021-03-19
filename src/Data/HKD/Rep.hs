{-# Language Trustworthy #-}

module Data.HKD.Rep
( type (%)
, FIndexable(..)
, FRepresentable(..)
, fdistribute
, fdistrib
, fcollect
, fcotraverse
, pattern FTabulate
, fliftD2
, fliftD3
, fliftD4
, fliftD5
-- * DerivingVia
, FDist(..)
-- * FFunctor
, ffmapFDist
-- * FApply
, fliftA2FDist
-- * FApplicative
, fpureFDist
-- * FMonad
, fbindFDist 
-- * Others
, faskFDist
, ftraceFDist
, ifmapFDist
, iffoldMapFDist
, iftraverseFDist
-- * Default logarithms
, FLogarithm(..)
, FTab(..)
, findexFLogarithm
, ftabulateFLogarithm
, ftabulateGeneric
, findexGeneric
, fscatterGeneric
, fscatterDefault
, Indices

-- * Uniqueness of logarithms
, flogToFLogarithm
, flogFromFLogarithm
, geqFLog
, gcompareFLog

-- * Logarithm lens
, _flogarithm
, _flog
, _flogGEq

-- * LKD
, LKD(..)
, lowerLogarithm
, liftLogarithm

-- * HKD
, HKD(..)
, Atkey(..)

-- * Constrained Representable operations
, FAll(..)
, cfdistrib
) where

import Data.Functor.Rep.Internal
