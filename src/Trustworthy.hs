{-# LANGUAGE Unsafe #-}

-- | 
-- Copyright   : (c) Edward Kmett 2021
-- License     : BSD-2-Clause OR Apache-2.0
-- Maintainer  : Edward Kmett <ekmett@gmail.com>
-- Stability   : experimental
-- Portability : non-portable
--
-- Safe Haskell has a pretty egregious design flaw.
--
-- If you use @-Winferred-safe-imports@, which is really
-- your only way to get visibility into upstream safety,
-- there is generally no way to escape the warnings it
-- gives except to expect upstream packages to fix their code.
--
-- The "fix" is to import a module that isn't @Safe@ so
-- I can forcibly downgrade myself to @Trustworthy@.
--
-- Ideally, I'd just have @{-# LANGUAGE TrustworthyOrBetter #-}@
-- extension, but every time I've asked for it, I've been
-- told this is against the spirit of the extension, which
-- as far as I can tell exists solely to make my life hell.

module Trustworthy () where
