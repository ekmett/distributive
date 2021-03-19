{-# Language Trustworthy #-}

-- |
-- Copyright   : (C) 2011-2021 Edward Kmett,
--               (c) 2017-2021 Aaron Vargo,
--               (c) 2021 Oleg Grenrus
-- License     : BSD-style (see the file LICENSE)
-- Maintainer  : Edward Kmett <ekmett@gmail.com>
-- Stability   : provisional
-- Portability : non-portable (ghc 8.6+)
--
-- Heterogeneous vectors.

module Data.HKD.Record
( Index(Index, IndexZ, IndexS)
, toIndex
, Length
, KnownLength
, lowerFin, liftFin
--, lowerVec, liftVec
, len
, Record(Nil, Cons)
, findexRecord
, withLen
) where

import Data.HKD.Internal.Index
import Data.HKD.Internal.Record
