{-# LANGUAGE CPP #-}
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
import qualified Data.Monoid as Monoid
import Data.Orphans ()

#if MIN_VERSION_base(4,4,0)
import Data.Complex
#endif
#if (defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 707) || defined(MIN_VERSION_tagged)
import Data.Proxy
#endif
#ifdef MIN_VERSION_tagged
import Data.Tagged
#endif

#ifdef HLINT
{-# ANN module "hlint: ignore Use section" #-}
#endif

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

instance Distributive Monoid.Dual where
  collect f  = Monoid.Dual . fmap (Monoid.getDual . f)
  distribute = Monoid.Dual . fmap Monoid.getDual

instance Distributive Monoid.Product where
  collect f  = Monoid.Product . fmap (Monoid.getProduct . f)
  distribute = Monoid.Product . fmap Monoid.getProduct

instance Distributive Monoid.Sum where
  collect f  = Monoid.Sum . fmap (Monoid.getSum . f)
  distribute = Monoid.Sum . fmap Monoid.getSum

#if MIN_VERSION_base(4,4,0)
instance Distributive Complex where
  distribute wc = fmap realP wc :+ fmap imagP wc where
    -- Redefine realPart and imagPart to avoid incurring redundant RealFloat
    -- constraints on older versions of base
    realP (r :+ _) = r
    imagP (_ :+ i) = i
#endif
