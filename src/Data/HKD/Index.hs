{-# Language GeneralizedNewtypeDeriving #-}
{-# Language Unsafe #-}

-- |
-- Copyright   : (C) 2021 Edward Kmett,
-- License     : BSD-2-style OR Apache-2.0
-- Maintainer  : Edward Kmett <ekmett@gmail.com>
-- Stability   : provisional
-- Portability : non-portable

module Data.HKD.Index
( Index(Index,IndexZ,IndexS)
, lowerFin, liftFin
, pattern IntIndex
, toIndex
, Length
, KnownLength
, len
) where

import Data.HKD.Index.Internal
