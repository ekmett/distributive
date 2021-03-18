{-# Language Trustworthy #-}

module Data.Distributive.Vec
( Fin(Fin,FinZ,FinS)
, pattern IntFin
, toFin
, Vec(Vec,toVector)
, FromVector(..)
, pattern V
, withDim
) where

import Data.Distributive.Internal.Fin
import Data.Distributive.Internal.Vec
