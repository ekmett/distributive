{-# Language Trustworthy #-}

module Data.HKD.Rep
( type (%)
, FIndexable(..)
, FRepresentable(..)
, fdistrib
, fdistribute
, fcollect
, fcotraverse
, pattern FTabulate
-- * DerivingVia
, FDist(..)
-- * FFunctor
, ffmapRep
-- * FApply
, fliftR2
, fliftR3
, fliftR4
, fliftR5
-- * FApplicative
, fpureRep
-- * FMonad
, fbindRep
-- * Others
, faskRep
, ftraceRep
, ifmapRep
, iffoldMapRep
, iftraverseRep
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
