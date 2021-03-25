{-# Language Unsafe #-}

module Data.Distributive {-# DEPRECATED "Import Data.Rep" #-} 
( Distributive
, collect
, cotraverse
, distribute
) where

import Data.Rep

type Distributive = Representable
