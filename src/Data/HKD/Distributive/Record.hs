{-# Language ExplicitNamespaces #-}
{-# Language Trustworthy #-}
module Data.HKD.Distributive.Record
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

import Data.HKD.Distributive.Internal.Index
import Data.HKD.Distributive.Internal.Record
