-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Distributive
-- Copyright   :  (C) 2011 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  portable
--
----------------------------------------------------------------------------
module Data.Distributive 
  ( Distributive(..)
  , fmapDefault
  , cotraverse
  , comapM
  ) where

import Control.Applicative
import Control.Monad (liftM)
import Control.Monad.Trans.Identity
import Control.Monad.Trans.Reader
import Control.Monad.Instances ()
import Data.Functor.Identity

-- | This is the categorical dual of 'Traversable'. However, there appears
-- to be little benefit to allow the distribution via an arbitrary comonad
-- so we restrict ourselves to 'Functor'.
-- 
-- Minimal complete definition: 'distribute' or 'collect'
--
-- To be distributable a container will need to have a way to consistently
-- zip a potentially infinite number of copies of itself. This effectively
-- means that the holes in all values of that type, must have the same 
-- cardinality, fixed sized vectors, infinite streams, functions, etc.
-- and no extra information to try to merge together.

class Functor g => Distributive g where
  -- | The dual of 'Data.Traversable.sequence'
  -- 
  -- > distribute = collect id
  distribute  :: Functor f => f (g a) -> g (f a)
  distribute  = collect id

  -- | 
  -- > collect   = distribute . fmap f
  collect     :: Functor f => (a -> g b) -> f a -> g (f b)
  collect f   = distribute . fmap f

  -- | 
  -- > distributeM = fmap unwrapMonad . distribute . WrapMonad
  distributeM :: Monad m => m (g a) -> g (m a)
  distributeM = fmap unwrapMonad . distribute . WrapMonad 

  -- | 
  -- > collectM = distributeM . liftM f
  collectM    :: Monad m => (a -> g b) -> m a -> g (m b)
  collectM f  = distributeM . liftM f

cotraverse :: (Functor f, Distributive g) => (f a -> b) -> f (g a) -> g b
cotraverse f = fmap f . distribute

comapM :: (Monad m, Distributive g) => (m a -> b) -> m (g a) -> g b
comapM f = fmap f . distributeM

instance Distributive Identity where
  collect f = Identity . fmap (runIdentity . f)
  distribute = Identity . fmap runIdentity

instance Distributive ((->)e) where
  distribute a e = fmap ($e) a

instance Distributive g => Distributive (ReaderT e g) where
  distribute a = ReaderT $ \e -> collect (flip runReaderT e) a

instance Distributive g => Distributive (IdentityT g) where
  collect f = IdentityT . collect (runIdentityT . f)

-- | Every 'Distributive' is a 'Functor'. This is a valid default definition.
fmapDefault :: Distributive g => (a -> b) -> g a -> g b
fmapDefault f = cotraverse (f . runIdentity) . Identity

