{-# Language Trustworthy #-}
{-# Language PatternSynonyms #-}

-- Copyright   : (C) 2021 Edward Kmett,
-- License     : BSD-2-Clause OR Apache-2.0
-- Maintainer  : Edward Kmett <ekmett@gmail.com>
-- Stability   : provisional
-- Portability : non-portable
--
-- @'Fin' n@ is a natural number < @n@.
--
-- Here we represent them internally by an actual 'Int'
-- enabling the data type to be efficiently unpacked into
-- other constructors.
--
-- This compromises the use of 'Fin' for _very large_ numbers.
-- but for many uses involving containers or compilers, this
-- is a good balance.

module Numeric.Fin
( Fin(Fin,FZ,FS,fromFin,KnownFZ,KnownFS)
, pattern IntFin
, toFin
, absurdFin
) where

import Numeric.Fin.Internal
