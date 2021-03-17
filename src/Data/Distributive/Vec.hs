{-# Language PatternSynonyms #-}
{-# Language Trustworthy #-}

module Data.Distributive.Vec
( Fin(Fin,FZ,FS)
, pattern IntFin
, toFin
, Vec(Vec,toVector)
, FromVector(..)
, pattern V
, withDim
) where

import Data.Distributive.Internal.Fin
import Data.Distributive.Internal.Vec
