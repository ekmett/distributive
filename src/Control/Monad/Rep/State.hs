{-# Language CPP #-}
{-# Language Trustworthy #-}

-- |
-- Copyright   : (c) Edward Kmett 2011-2021,
--               (c) Sjoerd Visscher 2011
-- License     : BSD-2-Clause OR Apache-2.0
-- Maintainer  : Edward Kmett <ekmett@gmail.com>
-- Stability   : experimental
-- Portability : non-portable
--
-- A generalized State monad, parameterized by a 'Representable' functor.
-- The 'Log' of that functor serves as the state.

module Control.Monad.Rep.State
  ( State
  , pattern State
  , runState
  , evalState
  , execState
  , mapState
  , StateT(.., StateT, runStateT)
  , evalStateT
  , execStateT
  , mapStateT
  , liftCallCC
  , liftCallCC'
  , liftCatch
  , liftListen
  , liftPass
  ) where

import Control.Applicative
import Control.Monad
import Control.Monad.Cont.Class
import Control.Monad.Error.Class
import Control.Monad.Fail
import Control.Monad.Fix
import Control.Monad.Reader.Class
import Control.Monad.Signatures
import Control.Monad.State.Class
import Control.Monad.Trans.Class
import Control.Monad.Writer.Class
import Data.Coerce
import Data.Data
import Data.Function.Coerce
import Data.Functor.Contravariant
import Data.Functor.Identity
import Data.Rep
import Data.HKD
import GHC.Generics

-- | A memoized state monad parameterized by a 'Representable' functor @g@, where
-- 'Log' g is the state to carry.
--
-- 'return' leaves the state unchanged, while '(>>=)' uses the final state of
-- the first computation as the initial state of the second.
type State g = StateT g Identity

pattern State :: Representable g => (Log g -> (a, Log g)) -> State g a
pattern State { runState } <- StateT (Coerce runState)

{-# complete State #-}

-- | Evaluate a state computation with the given initial state
-- and return the final value, discarding the final state.
--
-- * @'evalState' m s = 'fst' ('runState' m s)@
evalState
  :: Representable g
  => State g a  -- ^state-passing computation to execute
  -> Log g      -- ^initial value
  -> a          -- ^return value of the state computation
evalState m s = fst (runState m s)
{-# inline evalState #-}

-- | Evaluate a state computation with the given initial state
-- and return the final state, discarding the final value.
--
-- * @'execState' m s = 'snd' ('runState' m s)@
execState
  :: Representable g
  => State g a  -- ^state-passing computation to execute
  -> Log g      -- ^initial value
  -> Log g      -- ^final state
execState m s = snd (runState m s)
{-# inline execState #-}

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
{-# inline mapState #-}

-- | A state transformer monad parameterized by:
--
--   * @g@ - A representable functor used to memoize results for a state @Log g@
--
--   * @m@ - The inner monad.
--
-- The 'return' function leaves the state unchanged, while @>>=@ uses
-- the final state of the first computation as the initial state of
-- the second.
type role StateT nominal nominal nominal
newtype StateT g m a = StateDistT
  { runStateDistT :: g (m (a, Log g))
  } deriving (Generic) -- Generic1 would require me to flip the (,) breaking State compat

deriving stock instance
  ( Typeable g
  , Typeable m
  , Typeable a
  , Data (g (m (a, Log g)))
  ) => Data (StateT g m a)

-- | Emulate a traditional state monad
pattern StateT :: Representable g => (Log g -> m (a, Log g)) -> StateT g m a
pattern StateT { runStateT } = StateDistT (Tabulate runStateT) 

{-# complete StateT #-}

mapStateT :: Functor g => (m (a, Log g) -> n (b, Log g)) -> StateT g m a -> StateT g n b
mapStateT = \f -> StateDistT #. fmap f .# runStateDistT
{-# inline mapStateT #-}

-- | Evaluate a state computation with the given initial state
-- and return the final value, discarding the final state.
--
-- * @'evalStateT' m s = 'fmap' 'fst' ('runStateT' m s)@
evalStateT :: (Representable g, Functor m) => StateT g m a -> Log g -> m a
evalStateT = \m -> fmap fst . runStateT m 
{-# inline evalStateT #-}

-- | Evaluate a state computation with the given initial state
-- and return the final state, discarding the final value.
--
-- * @'execStateT' m s = 'fmap' 'snd' ('runStateT' m s)@
execStateT :: (Representable g, Functor m) => StateT g m a -> Log g -> m (Log g)
execStateT = \m -> fmap snd . runStateT m
{-# inline execStateT #-}

instance (Functor g, Functor m) => Functor (StateT g m) where
  fmap = \f -> StateDistT #. fmap (fmap (\ ~(a, s) -> (f a, s))) .# runStateDistT
  {-# inline fmap #-}

instance (Representable g, Functor m, Monad m) => Applicative (StateT g m) where
  pure = StateDistT #. leftAdjunctRep pure
  {-# inline pure #-}
  (<*>) = \mf ma -> mf >>= \f -> fmap f ma
  {-# inline (<*>) #-}

instance (Representable g, Monad m) => Monad (StateT g m) where
  (>>=) = \(StateDistT m) f -> StateDistT $ fmap (>>= rightAdjunctRep (runStateT . f)) m
  {-# inline (>>=) #-}
#if !(MIN_VERSION_base(4,13,0))
  fail = lift . Control.Monad.fail
  {-# inline fail #-}
#endif

instance (Representable g, MonadFail m) => MonadFail (StateT g m) where
  fail = lift . Control.Monad.Fail.fail
  {-# inline fail #-}

instance Representable f => MonadTrans (StateT f) where
  lift = \m -> StateT $ \s -> (,s) <$> m
  {-# inline lift #-}

liftStateT :: (Representable f, Functor m) => m a -> StateT f m a
liftStateT = \m -> StateT $ \s -> (,s) <$> m
{-# inline liftStateT #-}

instance (Representable g, Monad m, Log g ~ s) => MonadState s (StateT g m) where
  get = StateT $ \s -> pure (s, s)
  {-# inline get #-}
  put = \s -> StateDistT $ pureRep $ pure ((),s)
  {-# inline put #-}
  state = \f -> StateT $ pure . f
  {-# inline state #-}

instance (Representable g, MonadReader e m) => MonadReader e (StateT g m) where
  ask = lift ask
  {-# inline ask #-}
  local = mapStateT . local
  {-# inline local #-}
  reader = lift . reader
  {-# inline reader #-}

instance (Representable g, MonadWriter w m) => MonadWriter w (StateT g m) where
  tell = lift . tell
  {-# inline tell #-}
  listen = liftListen listen
  {-# inline listen #-}
  pass = liftPass pass
  {-# inline pass #-}

liftListen :: (Representable f, Functor m) => Listen w m (a, Log f) -> Listen w (StateT f m) a
liftListen = \listen' -> mapStateT $ 
  fmap (\((a,s'), w) -> ((a,w), s')) . listen'
{-# inline liftListen #-}

liftPass :: (Representable f, Functor m) => Pass w m (a, Log f) -> Pass w (StateT f m) a
liftPass = \pass' -> mapStateT $ \m -> pass' $ (\((a, f), s') -> ((a, s'), f)) <$> m
{-# inline liftPass #-}

instance (Representable g, MonadCont m) => MonadCont (StateT g m) where
  callCC = liftCallCC' callCC
  {-# inline callCC #-}

-- | Uniform lifting of a @callCC@ operation to the new monad.
-- This version rolls back to the original state on entering the
-- continuation.
liftCallCC
  :: Representable g
  => ((((a,Log g) -> m (b,Log g)) -> m (a,Log g)) -> m (a,Log g))
  -> ((a -> StateT g m b) -> StateT g m a)
  -> StateT g m a
liftCallCC = \callCC' f -> StateT $ \s ->
  callCC' $ \c ->
  runStateT (f (\a -> StateDistT $ pureRep $ c (a, s))) s
{-# inline liftCallCC #-}

-- | In-situ lifting of a @callCC@ operation to the new monad.
-- This version uses the current state on entering the continuation.
-- It does not satisfy the uniformity property (see "Control.Monad.Signatures").
liftCallCC'
  :: Representable g => ((((a,Log g) -> m (b,Log g)) -> m (a,Log g)) -> m (a,Log g))
  -> ((a -> StateT g m b) -> StateT g m a)
  -> StateT g m a
liftCallCC' = \callCC' f -> StateT $ \s ->
  callCC' $ \c -> runStateT (f (\a -> StateT $ \s' -> c (a, s'))) s
{-# inline liftCallCC' #-}

instance (Representable f, MonadPlus m) => Alternative (StateT f m) where
  empty = liftStateT mzero
  {-# inline empty #-}
  (<|>) = \(StateDistT fm) (StateDistT fn) -> StateDistT (liftR2 mplus fm fn)
  {-# inline (<|>) #-}

instance (Representable f, MonadPlus m) => MonadPlus (StateT f m)

instance (Representable f, MonadError e m) => MonadError e (StateT f m) where
  throwError = lift . throwError
  {-# inline throwError #-}
  catchError = liftCatch catchError
  {-# inline catchError #-}

data DCatch x y z f = DCatch (f x) (y -> f z)

instance FFunctor (DCatch x y m) where
  ffmap = \ f (DCatch l r) -> DCatch (f l) (f . r)
  {-# inline ffmap #-}

-- | Lift a @catchE@ operation to the new monad.
liftCatch :: Representable f => Catch e m (a, Log f) -> Catch e (StateT f m) a
liftCatch = \catchE (StateDistT m) h ->
  StateDistT $ distrib (DCatch m (runStateDistT #. h)) $ \(DCatch m' h') -> coerce catchE m' h'
{-# INLINE liftCatch #-}

instance (Representable f, MonadFix m) => MonadFix (StateT f m) where
  -- mfix f = StateT $ \s -> mfix \ ~(a, _) -> runStateT (f a) s
  mfix = \f ->
    StateDistT $ distrib (FCompose (runStateDistT #. f)) $ \f' -> mfix (coerce f' . fst)
  {-# inline mfix #-}

instance (Representable f, Contravariant m) => Contravariant (StateT f m) where
  contramap = \f (StateDistT m) -> StateDistT $ contramap (\ ~(a, s') -> (f a, s')) <$> m
  {-# inline contramap #-}
