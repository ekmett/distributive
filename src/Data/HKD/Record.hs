{-# Language Trustworthy #-}

module Data.HKD.Record
( Index(Index, IndexZ, IndexS)
, toIndex
, Length
, KnownLength
, lowerFin, liftFin
, len
, Record(Nil, Cons)
, withLen
, All
) where

import Data.HKD.Internal.Index
import Data.HKD.Internal.Record
