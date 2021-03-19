{-# Language Trustworthy #-}

-- |
-- Copyright   : (C) 2021 Edward Kmett,
-- License     : BSD-2-Clause OR Apache-2.0
-- Maintainer  : Edward Kmett <ekmett@gmail.com>
-- Stability   : provisional
-- Portability : non-portable (ghc 8.6+)

module Data.Distributive.Vec
( Vec(Vec,toVector)
, FromVector(..)
, pattern V
, withDim
) where

import Data.Distributive.Internal.Vec
