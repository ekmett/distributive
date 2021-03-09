{-# Language CPP #-}
{-# Language FlexibleContexts #-}
{-# Language FlexibleInstances #-}
{-# Language MultiParamTypeClasses #-}
{-# Language PatternSynonyms #-}
{-# Language TypeFamilies #-}
{-# Language TypeSynonymInstances #-}
{-# Language UndecidableInstances #-}
{-# Language ViewPatterns #-}
-- |
-- Module      :  Control.Monad.Distributive.State
-- Copyright   :  (c) Edward Kmett 2011-2021
--                (c) Sjoerd Visscher 2011
-- License     :  BSD3
--
-- Maintainer  :  ekmett@gmail.com
-- Stability   :  experimental
--
-- A generalized State monad, parameterized by a 'Distributive' functor.
-- The 'Log' of that functor serves as the state.
module Control.Monad.Distributive.State
  ( State
  , pattern State
  , runState
  , evalState
  , execState
  , mapState
  , StateT(StateDistT)
  , pattern StateT

  , runStateT
  , evalStateT
  , execStateT
  , mapStateT
  , liftCallCC
  , liftCallCC'
  , MonadState(..)
  ) where

import Control.Monad
import Control.Monad.State.Class
import Control.Monad.Cont.Class
import Control.Monad.Reader.Class
import Control.Monad.Writer.Class
import Control.Monad.Trans.Class
import Data.Functor.Identity
import Data.Distributive
import Data.Distributive.Util

-- | A memoized state monad parameterized by a 'Distributive' functor @g@, where
-- 'Log' g is the state to carry.
--
-- 'return' leaves the state unchanged, while '(>>=)' uses the final state of
-- the first computation as the initial state of the second.
type State g = StateT g Identity

-- | Unwrap a state monad computation as a function.
-- (The inverse of 'state'.)
runState
  :: Distributive g
  => State g a   -- ^ state-passing computation to execute
  -> Log g       -- ^ initial state
  -> (a, Log g)  -- ^ return value and final state
runState m = runIdentity . runStateT m

pattern State :: Distributive g => (Log g -> (a, Log g)) -> State g a
pattern State f <- (runState -> f) where
  State f = state f

-- | Evaluate a state computation with the given initial state
-- and return the final value, discarding the final state.
--
-- * @'evalState' m s = 'fst' ('runState' m s)@
evalState
  :: Distributive g
  => State g a  -- ^state-passing computation to execute
  -> Log g      -- ^initial value
  -> a          -- ^return value of the state computation
evalState m s = fst (runState m s)

-- | Evaluate a state computation with the given initial state
-- and return the final state, discarding the final value.
--
-- * @'execState' m s = 'snd' ('runState' m s)@
execState
  :: Distributive g
  => State g a  -- ^state-passing computation to execute
  -> Log g      -- ^initial value
  -> Log g      -- ^final state
execState m s = snd (runState m s)

-- | Map both the return value and final state of a computation using
-- the given function.
--
-- * @'runState' ('mapState' f m) = f . 'runState' m@
mapState
  :: Functor g
  => ((a, Log g) -> (b, Log g))
  -> State g a
  -> State g b
mapState f = mapStateT (Identity #. f .# runIdentity)

-- | A state transformer monad parameterized by:
--
--   * @g@ - A representable functor used to memoize results for a state @Log g@
--
--   * @m@ - The inner monad.
--
-- The 'return' function leaves the state unchanged, while @>>=@ uses
-- the final state of the first computation as the initial state of
-- the second.
newtype StateT g m a = StateDistT
  { runStateDistT :: g (m (a, Log g))
  }

-- | Emulate a traditional state monad
pattern StateT :: Distributive g => (Log g -> m (a, Log g)) -> StateT g m a
pattern StateT f <- StateDistT (index -> f) where
  StateT f = StateDistT (tabulate f)

runStateT :: Distributive g => StateT g m a -> Log g -> m (a, Log g)
runStateT = index .# runStateDistT

mapStateT :: Functor g => (m (a, Log g) -> n (b, Log g)) -> StateT g m a -> StateT g n b
mapStateT f = StateDistT #. fmap f .# runStateDistT

-- | Evaluate a state computation with the given initial state
-- and return the final value, discarding the final state.
--
-- * @'evalStateDistT m s = 'liftM' 'fst' ('runStateDistT m s)@
evalStateT :: (Distributive g, Monad m) => StateT g m a -> Log g -> m a
evalStateT m s = do
  (a, _) <- runStateT m s
  return a

-- | Evaluate a state computation with the given initial state
-- and return the final state, discarding the final value.
--
-- * @'execStateDistT m s = 'liftM' 'snd' ('runStateDistT m s)@
execStateT :: (Distributive g, Monad m) => StateT g m a -> Log g -> m (Log g)
execStateT m s = do
  (_, s') <- runStateT m s
  return s'

instance (Functor g, Functor m) => Functor (StateT g m) where
  fmap f = StateDistT #. fmap (fmap (\ ~(a, s) -> (f a, s))) .# runStateDistT

instance (Distributive g, Functor m, Monad m) => Applicative (StateT g m) where
  pure = StateDistT #. leftAdjunctDist return
  mf <*> ma = mf >>= \f -> fmap f ma

instance (Distributive g, Monad m) => Monad (StateT g m) where
  StateDistT m >>= f = StateDistT $ fmap (>>= rightAdjunctDist (runStateT . f)) m

instance Distributive f => MonadTrans (StateT f) where
  lift m = StateT $ \s -> liftM (\a -> (a, s)) m

instance (Distributive g, Monad m, Log g ~ s) => MonadState s (StateT g m) where
  get = StateT $ \s -> pure (s, s)
  put s = StateDistT $ pureDist $ pure ((),s)
  state f = StateT $ pure . f

instance (Distributive g, MonadReader e m) => MonadReader e (StateT g m) where
  ask = lift ask
  local = mapStateT . local

instance (Distributive g, MonadWriter w m) => MonadWriter w (StateT g m) where
  tell = lift . tell
  listen = mapStateT $ \ma -> do
    ((a,s'), w) <- listen ma
    return ((a,w), s')
  pass = mapStateT $ \ma -> pass $ do
    ((a, f), s') <- ma
    return ((a, s'), f)

instance (Distributive g, MonadCont m) => MonadCont (StateT g m) where
  callCC = liftCallCC' callCC

-- | Uniform lifting of a @callCC@ operation to the new monad.
-- This version rolls back to the original state on entering the
-- continuation.
liftCallCC
  :: Distributive g
  => ((((a,Log g) -> m (b,Log g)) -> m (a,Log g)) -> m (a,Log g))
  -> ((a -> StateT g m b) -> StateT g m a)
  -> StateT g m a
liftCallCC callCC' f = StateT $ \s ->
  callCC' $ \c ->
  runStateT (f (\a -> StateDistT $ pureDist $ c (a, s))) s

-- | In-situ lifting of a @callCC@ operation to the new monad.
-- This version uses the current state on entering the continuation.
-- It does not satisfy the laws of a monad transformer.
liftCallCC'
  :: Distributive g => ((((a,Log g) -> m (b,Log g)) -> m (a,Log g)) -> m (a,Log g))
  -> ((a -> StateT g m b) -> StateT g m a)
  -> StateT g m a
liftCallCC' callCC' f = StateT $ \s ->
  callCC' $ \c ->
  runStateT (f (\a -> StateT $ \s' -> c (a, s'))) s
