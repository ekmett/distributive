{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Distributive
-- Copyright   :  (C) 2011-2016 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  portable
--
----------------------------------------------------------------------------
module Data.Distributive.Generic
  ( GDistributive(..)
  , genericDistribute
  ) where

import Data.Distributive
import GHC.Generics

-- | 'distribute' derived from a 'Generic1' type
--
-- This can be used to easily produce a 'Distributive' instance for a
-- type with a 'Generic1' instance,
--
-- > data V2 a = V2 a a deriving (Show, Functor, Generic1)
-- > instance Distributive V2' where distribute = genericDistribute
genericDistribute  :: (Functor f, Generic1 g, GDistributive (Rep1 g)) => f (g a) -> g (f a)
genericDistribute = to1 . gdistribute . fmap from1

-- Can't distribute over,
--   * sums (:+:)
--   * K1
class GDistributive g where
  gdistribute :: Functor f => f (g a) -> g (f a)

instance GDistributive U1 where
  gdistribute _ = U1
  {-# INLINE gdistribute #-}

instance (GDistributive a, GDistributive b) => GDistributive (a :*: b) where
  gdistribute f = gdistribute (fmap fstP f) :*: gdistribute (fmap sndP f) where
    fstP (l :*: _) = l
    sndP (_ :*: r) = r
  {-# INLINE gdistribute #-}

instance (Functor a, Distributive a, GDistributive b) => GDistributive (a :.: b) where
  gdistribute = Comp1 . fmap gdistribute . distribute . fmap unComp1
  {-# INLINE gdistribute #-}

instance GDistributive Par1 where
  gdistribute = Par1 . fmap unPar1
  {-# INLINE gdistribute #-}

instance Distributive f => GDistributive (Rec1 f) where
  gdistribute = Rec1 . distribute . fmap unRec1
  {-# INLINE gdistribute #-}

instance GDistributive f => GDistributive (M1 i c f) where
  gdistribute = M1 . gdistribute . fmap unM1
  {-# INLINE gdistribute #-}
