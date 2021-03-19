{-# Language Trustworthy #-}

module Data.HKD.Distributive
( type (%)
, FIndexable(..)
, FDistributive(..)
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
-- * FRepeat
, fpureFDist
-- * FApply
, fliftA2FDist
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
, ftabulateRep
, findexRep
, fscatterRep
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

-- * Constrained Distributive operations
, FAll(..)
, cfdistrib
) where

import Data.Distributive.Internal
