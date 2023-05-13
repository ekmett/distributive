{-# Language Trustworthy #-}

-- |
-- Copyright   : (C) 2021 Edward Kmett,
-- License     : BSD-2-Style OR Apache-2.0
-- Maintainer  : Edward Kmett <ekmett@gmail.com>
-- Stability   : provisional
-- Portability : non-portable
--
-- Heterogeneous vectors.

module Data.HKD.Record
( Index(Index, IZ, IS, KnownIZ, KnownIS)
, toIndex
, Length
, KnownLength
, lowerFin, liftFin
--, lowerVec, liftVec
, len
, Record(Nil, Cons)
, withLen
) where

import Data.HKD.Index.Internal
import Data.HKD.Record.Internal
