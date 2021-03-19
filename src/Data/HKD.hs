{-# Language GeneralizedNewtypeDeriving #-}
{-# language Trustworthy #-}

-- |
-- Copyright :  (c) 2019-2021 Edward Kmett
--              (c) 2019 Oleg Grenrus
--              (c) 2017-2021 Aaron Vargo
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable
--
-- "Higher-Kinded Data" such as it is
--
-- Simple usage:
--
-- @
-- data Record f = Record
--   { fieldInt    :: f Int
--   , fieldString :: f String
--   , fieldSome   :: 'Some' f
--   } deriving ('Generic1', 'FFunctor', 'FFoldable', 'FTraversable')
-- @
--
-- Generically derived 'FApply' and 'FApplicative':
--
-- @
-- data Record f = Record
--   { fieldInt    :: f Int
--   , fieldString :: f String
--   } deriving ('Generic1', 'FApply', 'FApplicative')
-- @
module Data.HKD
(
-- * "Natural" transformations
  type (~>)
-- * Functor
, FFunctor(..)
, gffmap
-- * Foldable
, FFoldable(..)
, gffoldMap
, flength
, ftraverse_
, ffor_
-- * Traversable
, FTraversable(..)
, ViaFTraversable(..)
, ffmapDefault
, ffoldMapDefault
, ffor
, fsequence
, FApply(..)
, FApplicative(..)
, ViaFApplicative(..)
-- * FMonad
, FMonad(..)
, ViaFMonad(..)
, fbindInner
, fbindOuter
-- * FEq
, EqC, FEq
-- * FOrd
, OrdC', OrdC, FOrd
-- * Higher kinded data
-- | See also "Data.Some" in @some@ package. This package provides instances for it.
, F0(..)
, F1(..)
, F2(..)
, F3(..)
, F4(..)
, F5(..)
, FConstrained(..)
, FCompose(..)
, NT(..)
, Lim(..), traverseLim
, Dict1(..)
, Dicts(..)
, HKD(..), mapHKD
, LKD(..)
) where

import Data.HKD.Classes
import Data.HKD.Types

