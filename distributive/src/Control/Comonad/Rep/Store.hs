{-# Language FlexibleContexts #-}
{-# Language FlexibleInstances #-}
{-# Language MultiParamTypeClasses #-}
{-# Language Safe #-}
{-# Language TypeFamilies #-}
{-# Language UndecidableInstances #-}

-- |
-- Copyright   : (c) Edward Kmett 2011-2021
--               (c) Sjoerd Visscher 2011
-- License     : BSD-2-Clause OR Apache-2.0
-- Maintainer  : ekmett@gmail.com
-- Stability   : experimental
--
-- This is a generalized 'Store' 'Comonad', parameterized by a 'Representable' 'Functor'.
-- The representation of that 'Functor' serves as the index of the store.
--
-- This can be useful if the representable functor serves to memoize its
-- contents and will be inspected often.

module Control.Comonad.Rep.Store
( Store
, store
, runStore
, StoreT(..)
, storeT
, runStoreT
, ComonadStore(..)
) where

import Control.Comonad
-- import Control.Comonad.Cofree.Class
import Control.Comonad.Env.Class
import Control.Comonad.Hoist.Class
import Control.Comonad.Store.Class
import Control.Comonad.Traced.Class
import Control.Comonad.Trans.Class
import Control.Monad.Identity
import Data.Rep
import Data.Data
import Data.Foldable.WithIndex
import Data.Functor.WithIndex
import Data.Traversable.WithIndex
import GHC.Generics

-- | A memoized store comonad parameterized by a representable functor @g@, where
-- the representatation of @g@, @Log g@ is the index of the store.
--
type Store g = StoreT g Identity

-- | Construct a store comonad computation from a function and a current index.
-- (The inverse of 'runStore'.)
store :: Representable g
      => (Log g -> a)  -- ^ computation
      -> Log g         -- ^ index
      -> Store g a
store = storeT . Identity
{-# inline store #-}

-- | Unwrap a store comonad computation as a function and a current index.
-- (The inverse of 'store'.)
runStore :: Representable g
         => Store g a           -- ^ a store to access
         -> (Log g -> a, Log g) -- ^ initial state
runStore (StoreT (Identity ga) k) = (index ga, k)
{-# inline runStore #-}

-- ---------------------------------------------------------------------------
-- | A store transformer comonad parameterized by:
--
--   * @g@ - A representable functor used to memoize results for an index @Log g@
--
--   * @w@ - The inner comonad.
data StoreT g w a = StoreT (w (g a)) (Log g)
  deriving stock (Generic, Generic1, Functor, Foldable, Traversable)
  -- deriving anyclass (FunctorWithIndex (Log w, Log g))

deriving stock instance 
  ( Typeable g
  , Typeable w
  , Typeable a
  , Data (w (g a))
  , Data (Log g)
  ) => Data (StoreT g w a)

instance 
  ( FunctorWithIndex i w
  , FunctorWithIndex j g
  ) => FunctorWithIndex (i, j) (StoreT g w) where
  imap f (StoreT wg lg) = StoreT (imap (\i -> imap \j -> f (i,j)) wg) lg

instance 
  ( FoldableWithIndex i w
  , FoldableWithIndex j g
  ) => FoldableWithIndex (i, j) (StoreT g w) where
  ifoldMap f (StoreT wg _) = ifoldMap (\i -> ifoldMap \j -> f (i,j)) wg

instance 
  ( TraversableWithIndex i w
  , TraversableWithIndex j g
  ) => TraversableWithIndex (i, j) (StoreT g w) where
  itraverse f (StoreT wg lg) = (`StoreT` lg) <$> itraverse (\i -> itraverse \j -> f (i,j)) wg

storeT :: (Functor w, Representable g) => w (Log g -> a) -> Log g -> StoreT g w a
storeT = StoreT . fmap tabulate
{-# inline storeT #-}

runStoreT :: (Functor w, Indexable g) => StoreT g w a -> (w (Log g -> a), Log g)
runStoreT (StoreT w s) = (index <$> w, s)
{-# inline runStoreT #-}

instance (Comonad w, Representable g, Log g ~ s) => ComonadStore s (StoreT g w) where
  pos (StoreT _ s) = s
  {-# inline pos #-}
  peek s (StoreT w _) = extract w `index` s
  {-# inline peek #-}
  peeks f (StoreT w s) = extract w `index` f s
  {-# inline peeks #-}
  seek s (StoreT w _) = StoreT w s
  {-# inline seek #-}
  seeks f (StoreT w s) = StoreT w (f s)
  {-# inline seeks #-}

instance (ComonadApply w, Semigroup (Log g), Representable g) => ComonadApply (StoreT g w) where
  StoreT ff m <@> StoreT fa n = StoreT (apRep <$> ff <@> fa) (m <> n)
  {-# inline (<@>) #-}

instance (Applicative w, Monoid (Log g), Representable g) => Applicative (StoreT g w) where
  pure a = StoreT (pure (pureRep a)) mempty
  {-# inline pure #-}
  StoreT ff m <*> StoreT fa n = StoreT (apRep <$> ff <*> fa) (m `mappend` n)
  {-# inline (<*>) #-}

instance (Comonad w, Representable g) => Comonad (StoreT g w) where
  duplicate (StoreT wf s) = StoreT (extend (tabulate . StoreT) wf) s
  {-# inline duplicate #-}
  extract (StoreT wf s) = index (extract wf) s
  {-# inline extract #-}

instance Representable g => ComonadTrans (StoreT g) where
  lower (StoreT w s) = fmap (`index` s) w
  {-# inline lower #-}

instance ComonadHoist (StoreT g) where
  cohoist f (StoreT w s) = StoreT (f w) s
  {-# inline cohoist #-}

instance (ComonadTraced m w, Representable g) => ComonadTraced m (StoreT g w) where
  trace m = trace m . lower
  {-# inline trace #-}

instance (ComonadEnv m w, Representable g) => ComonadEnv m (StoreT g w) where
  ask = ask . lower
  {-# inline ask #-}

{-
instance (Representable g, ComonadCofree f w) => ComonadCofree f (StoreT g w) where
  unwrap (StoreT w s) = fmap (`StoreT` s) (unwrap w)
  {-# inline unwrap #-}
-}
