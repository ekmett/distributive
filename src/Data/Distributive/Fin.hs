{-# Language Trustworthy #-}
{-# Language PatternSynonyms #-}

module Data.Distributive.Fin
( Fin(Fin,FinZ,FinS,fromFin)
, pattern IntFin
, toFin
, absurdFin
) where

import Data.Distributive.Internal.Fin
