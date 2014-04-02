{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Distributive
-- Copyright   :  (C) 2011-2014 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  portable
--
----------------------------------------------------------------------------
module Data.Distributive
  ( Distributive(..)
  , cotraverse
  , comapM
  , genericDistribute
  ) where

import Control.Applicative
import Control.Applicative.Backwards
import Control.Monad (liftM)
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ < 707
import Control.Monad.Instances ()
#endif
import Control.Monad.Trans.Identity
import Control.Monad.Trans.Reader
import Data.Functor.Compose
import Data.Functor.Identity
import Data.Functor.Product
import Data.Functor.Reverse
import Data.Proxy
import Data.Tagged
import GHC.Generics

-- | This is the categorical dual of 'Traversable'.
--
-- Due to the lack of non-trivial comonoids in Haskell, we can restrict
-- ourselves to requiring a 'Functor' rather than
-- some Coapplicative class. Categorically every 'Distributive'
-- functor is actually a right adjoint, and so it must be 'Representable'
-- endofunctor and preserve all limits. This is a fancy way of saying it
-- isomorphic to `(->) x` for some x.
--
-- Minimal complete definition: 'distribute' or 'collect'
--
-- To be distributable a container will need to have a way to consistently
-- zip a potentially infinite number of copies of itself. This effectively
-- means that the holes in all values of that type, must have the same
-- cardinality, fixed sized vectors, infinite streams, functions, etc.
-- and no extra information to try to merge together.
--
class Functor g => Distributive g where
  -- | The dual of 'Data.Traversable.sequenceA'
  --
  -- >>> distribute [(+1),(+2)] 1
  -- [2,3]
  --
  -- @'distribute' = 'collect' 'id'@
  distribute  :: Functor f => f (g a) -> g (f a)
  distribute  = collect id

  -- |
  -- @'collect' f = 'distribute' . 'fmap' f@
  collect     :: Functor f => (a -> g b) -> f a -> g (f b)
  collect f   = distribute . fmap f

  -- | The dual of 'Data.Traversable.sequence'
  --
  -- @'distributeM' = 'fmap' 'unwrapMonad' . 'distribute' . 'WrapMonad'@
  distributeM :: Monad m => m (g a) -> g (m a)
  distributeM = fmap unwrapMonad . distribute . WrapMonad

  -- |
  -- @'collectM' = 'distributeM' . 'liftM' f@
  collectM    :: Monad m => (a -> g b) -> m a -> g (m b)
  collectM f  = distributeM . liftM f

-- | The dual of 'Data.Traversable.traverse'
--
-- @'cotraverse' f = 'fmap' f . 'distribute'@
cotraverse :: (Functor f, Distributive g) => (f a -> b) -> f (g a) -> g b
cotraverse f = fmap f . distribute

-- | The dual of 'Data.Traversable.mapM'
--
-- @'comapM' f = 'fmap' f . 'distributeM'@
comapM :: (Monad m, Distributive g) => (m a -> b) -> m (g a) -> g b
comapM f = fmap f . distributeM

instance Distributive Identity where
  collect f = Identity . fmap (runIdentity . f)
  distribute = Identity . fmap runIdentity

instance Distributive Proxy where
  collect _ _ = Proxy
  distribute _ = Proxy

instance Distributive (Tagged t) where
  collect f = Tagged . fmap (unTagged . f)
  distribute = Tagged . fmap unTagged

instance Distributive ((->)e) where
  distribute a e = fmap ($e) a

instance Distributive g => Distributive (ReaderT e g) where
  distribute a = ReaderT $ \e -> collect (flip runReaderT e) a

instance Distributive g => Distributive (IdentityT g) where
  collect f = IdentityT . collect (runIdentityT . f)

instance (Distributive f, Distributive g) => Distributive (Compose f g) where
  distribute = Compose . fmap distribute . collect getCompose

instance (Distributive f, Distributive g) => Distributive (Product f g) where
  distribute wp = Pair (collect fstP wp) (collect sndP wp) where
    fstP (Pair a _) = a
    sndP (Pair _ b) = b

instance Distributive f => Distributive (Backwards f) where
  distribute = Backwards . collect forwards

instance Distributive f => Distributive (Reverse f) where
  distribute = Reverse . collect getReverse

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

instance (Functor a, Functor b, GDistributive a, GDistributive b) => GDistributive (a :.: b) where
  gdistribute = Comp1 . fmap gdistribute . gdistribute . fmap unComp1
  {-# INLINE gdistribute #-}
  
instance GDistributive Par1 where
  gdistribute = Par1 . fmap unPar1
  {-# INLINE gdistribute #-}

instance GDistributive f => GDistributive (Rec1 f) where
  gdistribute = Rec1 . gdistribute . fmap unRec1
  {-# INLINE gdistribute #-}

instance GDistributive f => GDistributive (M1 i c f) where
  gdistribute = M1 . gdistribute . fmap unM1
  {-# INLINE gdistribute #-}
