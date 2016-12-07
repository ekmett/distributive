{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
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
module Data.Distributive
  ( Distributive(..)
  , cotraverse
  , comapM
  , fmapCollect
  ) where

import Control.Applicative
import Control.Applicative.Backwards
import Control.Monad (liftM)
#if __GLASGOW_HASKELL__ < 707
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
#if __GLASGOW_HASKELL__ >= 707 || defined(MIN_VERSION_tagged)
import Data.Proxy
#endif
#if __GLASGOW_HASKELL__ >= 800 || defined(MIN_VERSION_semigroups)
import qualified Data.Semigroup as Semigroup
#endif
#ifdef MIN_VERSION_tagged
import Data.Tagged
#endif
#if __GLASGOW_HASKELL__ >= 702
import GHC.Generics (U1(..), (:*:)(..), (:.:)(..), Par1(..), Rec1(..), M1(..))
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
-- isomorphic to @(->) x@ for some x.
--
-- To be distributable a container will need to have a way to consistently
-- zip a potentially infinite number of copies of itself. This effectively
-- means that the holes in all values of that type, must have the same
-- cardinality, fixed sized vectors, infinite streams, functions, etc.
-- and no extra information to try to merge together.
--
class Functor g => Distributive g where
#if __GLASGOW_HASKELL__ >= 707
  {-# MINIMAL distribute | collect #-}
#endif
  -- | The dual of 'Data.Traversable.sequenceA'
  --
  -- >>> distribute [(+1),(+2)] 1
  -- [2,3]
  --
  -- @
  -- 'distribute' = 'collect' 'id'
  -- 'distribute' . 'distribute' = 'id'
  -- @
  distribute  :: Functor f => f (g a) -> g (f a)
  distribute  = collect id

  -- |
  -- @
  -- 'collect' f = 'distribute' . 'fmap' f
  -- 'fmap' f = 'runIdentity' . 'collect' ('Identity' . f)
  -- 'fmap' 'distribute' . 'collect' f = 'getCompose' . 'collect' ('Compose' . f)
  -- @

  collect     :: Functor f => (a -> g b) -> f a -> g (f b)
  collect f   = distribute . fmap f

  -- | The dual of 'Data.Traversable.sequence'
  --
  -- @
  -- 'distributeM' = 'fmap' 'unwrapMonad' . 'distribute' . 'WrapMonad'
  -- @
  distributeM :: Monad m => m (g a) -> g (m a)
  distributeM = fmap unwrapMonad . distribute . WrapMonad

  -- |
  -- @
  -- 'collectM' = 'distributeM' . 'liftM' f
  -- @
  collectM    :: Monad m => (a -> g b) -> m a -> g (m b)
  collectM f  = distributeM . liftM f

-- | The dual of 'Data.Traversable.traverse'
--
-- @
-- 'cotraverse' f = 'fmap' f . 'distribute'
-- @
cotraverse :: (Distributive g, Functor f) => (f a -> b) -> f (g a) -> g b
cotraverse f = fmap f . distribute

-- | The dual of 'Data.Traversable.mapM'
--
-- @
-- 'comapM' f = 'fmap' f . 'distributeM'
-- @
comapM :: (Distributive g, Monad m) => (m a -> b) -> m (g a) -> g b
comapM f = fmap f . distributeM

instance Distributive Identity where
  collect f = Identity . fmap (runIdentity . f)
  distribute = Identity . fmap runIdentity

#if __GLASGOW_HASKELL__ >= 707 || defined(MIN_VERSION_tagged)
instance Distributive Proxy where
  collect _ _ = Proxy
  distribute _ = Proxy
#endif

#if defined(MIN_VERSION_tagged)
instance Distributive (Tagged t) where
  collect f = Tagged . fmap (unTagged . f)
  distribute = Tagged . fmap unTagged
#endif

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

#if __GLASGOW_HASKELL__ >= 800 || defined(MIN_VERSION_semigroups)
instance Distributive Semigroup.Min where
  collect f  = Semigroup.Min . fmap (Semigroup.getMin . f)
  distribute = Semigroup.Min . fmap Semigroup.getMin

instance Distributive Semigroup.Max where
  collect f  = Semigroup.Max . fmap (Semigroup.getMax . f)
  distribute = Semigroup.Max . fmap Semigroup.getMax

instance Distributive Semigroup.First where
  collect f  = Semigroup.First . fmap (Semigroup.getFirst . f)
  distribute = Semigroup.First . fmap Semigroup.getFirst

instance Distributive Semigroup.Last where
  collect f  = Semigroup.Last . fmap (Semigroup.getLast . f)
  distribute = Semigroup.Last . fmap Semigroup.getLast
#endif

#if MIN_VERSION_base(4,4,0)
instance Distributive Complex where
  distribute wc = fmap realP wc :+ fmap imagP wc where
    -- Redefine realPart and imagPart to avoid incurring redundant RealFloat
    -- constraints on older versions of base
    realP (r :+ _) = r
    imagP (_ :+ i) = i
#endif

-- | 'fmapCollect' is a viable default definition for 'fmap' given
-- a 'Distributive' instance defined in terms of 'collect'.
fmapCollect :: Distributive f => (a -> b) -> f a -> f b
fmapCollect f = runIdentity . collect (Identity . f)

#if __GLASGOW_HASKELL__ >= 702
instance Distributive U1 where
  distribute _ = U1

instance (Distributive a, Distributive b) => Distributive (a :*: b) where
  distribute f = distribute (fmap fstP f) :*: distribute (fmap sndP f) where
    fstP (l :*: _) = l
    sndP (_ :*: r) = r

instance (Distributive a, Distributive b) => Distributive (a :.: b) where
  distribute = Comp1 . fmap distribute . distribute . fmap unComp1

instance Distributive Par1 where
  distribute = Par1 . fmap unPar1

instance Distributive f => Distributive (Rec1 f) where
  distribute = Rec1 . distribute . fmap unRec1

instance Distributive f => Distributive (M1 i c f) where
  distribute = M1 . distribute . fmap unM1
#endif
