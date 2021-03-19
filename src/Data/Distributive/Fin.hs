{-# Language Trustworthy #-}
{-# Language PatternSynonyms #-}

-- Copyright   : (C) 2021 Edward Kmett,
-- License     : BSD-2-Clause OR Apache-2.0
-- Maintainer  : Edward Kmett <ekmett@gmail.com>
-- Stability   : provisional
-- Portability : non-portable (ghc 8.6+)

module Data.Distributive.Fin
( Fin(Fin,FinZ,FinS,fromFin)
, pattern IntFin
, toFin
, absurdFin
) where

import Data.Distributive.Internal.Fin
