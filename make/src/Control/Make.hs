{-# Language BlockArguments #-}
{-# Language ConstraintKinds #-}
{-# Language DefaultSignatures #-}
{-# Language DeriveAnyClass #-}
-- {-# Language DeriveDataTypeable #-}
{-# Language DeriveGeneric #-}
{-# Language DerivingStrategies #-}
{-# Language DerivingVia #-}
{-# Language FlexibleContexts #-}
{-# Language FlexibleInstances #-}
{-# Language GeneralizedNewtypeDeriving #-}
{-# Language PolyKinds #-}
{-# Language FunctionalDependencies #-}
{-# Language GADTs #-}
{-# Language ImportQualifiedPost #-}
{-# Language LambdaCase #-}
{-# Language MultiParamTypeClasses #-}
{-# Language OverloadedLists #-}
{-# Language RankNTypes #-}
{-# Language ScopedTypeVariables #-}
{-# Language StandaloneDeriving #-}
{-# Language TemplateHaskell #-}
{-# Language TupleSections #-}
{-# Language TypeFamilies #-}
{-# Language TypeOperators #-}
{-# Language UndecidableInstances #-}
{-# Language UnicodeSyntax #-}
{-# options_ghc -Wno-deprecations #-}

-- |
-- Copyright  : (c) Edward Kmett 2020-2021, Olle Fredriksson 2018-2020
-- License    : BSD-3-Clause
-- Maintainer : Edward Kmett <ekmett@gmail.com>
-- Stability  : experimental
-- Portability: non-portable
--
-- This is a version of Olle's @rock@ rebuilt as a monad transformer.

module Control.Make 
( TaskT(..)
, MonadTask(..)
, mapTask
, bindTask
, runTask
, GHashable
, trackM
, track
, memoise
, Cyclic(..)
, MemoEntry(..)
, memoiseWithCycleDetection
, ValueDeps(..)
, Traces
, verifyDependencies
, record
, TaskKind(..)
, Traced(..)
, tracing
, verifyTraces
, traceFetch
, ReverseDependencies
, trackReverseDependencies
, reachableReverseDependencies
) where

import Control.Applicative
import Control.Concurrent (ThreadId, myThreadId)
import Control.Exception 
import Control.Monad (join, unless)
import Control.Monad.Base
import Control.Monad.Catch as M
import Control.Monad.IO.Class
import Control.Monad.IO.Unlift
import Control.Monad.Primitive
import Control.Monad.Trans.Class
import Control.Monad.Trans.Control
import Control.Monad.Trans.Error
import Control.Monad.Trans.Except
import Control.Monad.Trans.Reader
import Control.Monad.Trans.State.Strict qualified as Strict
import Control.Monad.Trans.State.Lazy qualified as Lazy
import Control.Monad.Trans.Writer.Strict qualified as Strict
import Control.Monad.Trans.RWS.Lazy qualified as Lazy
import Control.Monad.Trans.RWS.Strict qualified as Strict
import Control.Monad.Trans.Writer.Lazy qualified as Lazy
import Data.Bifunctor
import Data.Constraint.Extras
import Data.Dependent.Sum
import Data.Dependent.HashMap (DHashMap)
import Data.Dependent.HashMap qualified as DHM
import Data.Functor.Classes
import Data.GADT.Compare
import Data.GADT.Show
import Data.HKD
import Data.Hashable
import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HM
import Data.HashSet 
import qualified Data.HashSet as HS
import Data.Kind
import Data.Maybe (fromMaybe)
import Data.Primitive.MVar
import Data.Primitive.MutVar
import Data.Some
import Data.Typeable
import GHC.Generics
import Text.Show.Deriving

-- McBride style indexed Cont
newtype TaskT f m (a :: Type)
  = TaskT { unTaskT :: (f ~> m) -> m a }
  deriving 
    ( Functor, Applicative, Monad
    , MonadIO
    , MonadUnliftIO
    , MonadThrow
    , MonadCatch
    , MonadMask
    ) via ReaderT (NT f m) m

deriving via (ReaderT (NT f m) m) instance MonadBase t m => MonadBase t (TaskT f m)
deriving via (ReaderT (NT f m) m) instance MonadBaseControl t m => MonadBaseControl t (TaskT f m)

instance MonadTrans (TaskT f) where
  lift m = TaskT \_ -> m

instance PrimMonad m => PrimMonad (TaskT f m) where
  type PrimState (TaskT f m) = PrimState m
  primitive k = TaskT \_ -> primitive k

class Monad m => MonadTask f m | m -> f where
  fetch :: f a -> m a
  default fetch :: (m ~ t n, MonadTask f n, MonadTrans t) => f a -> m a
  fetch = lift . fetch
  {-# inline fetch #-}

instance Monad m => MonadTask f (TaskT f m) where
  fetch f = TaskT \c -> c f 
  {-# inline fetch #-}

instance MonadTask f m => MonadTask f (ExceptT e m)
instance (MonadTask f m, Error e) => MonadTask f (ErrorT e m)
instance MonadTask f m => MonadTask f (ReaderT r m)
instance MonadTask f m => MonadTask f (Strict.StateT s m) 
instance MonadTask f m => MonadTask f (Lazy.StateT s m) 
instance (MonadTask f m, Monoid w) => MonadTask f (Strict.WriterT w m) 
instance (MonadTask f m, Monoid w) => MonadTask f (Lazy.WriterT w m) 
instance (MonadTask f m, Monoid w) => MonadTask f (Strict.RWST r w s m)
instance (MonadTask f m, Monoid w) => MonadTask f (Lazy.RWST r w s m)

mapTask :: (f ~> g) -> TaskT f m ~> TaskT g m
mapTask f (TaskT m) = TaskT \ c -> m (c . f)
{-# inline mapTask #-}

bindTask :: TaskT f m a -> (f ~> TaskT g m) -> TaskT g m a
bindTask m k = TaskT \ c -> unTaskT m \ x -> unTaskT (k x) c
{-# inline bindTask #-}

-- TODO: go transform to pull out the recursion
runTask :: ∀ f m. (f ~> TaskT f m) -> TaskT f m ~> m
runTask k = go where 
  go :: TaskT f m ~> m
  go m = unTaskT m (go . k)
{-# inline runTask #-}

type GHashable f = (GEq f, Hashable (Some f))

trackM
  :: (GHashable f, PrimMonad m)
  => (∀ b. f b -> b -> TaskT f m (g b))
  -> TaskT f m a -> TaskT f m (a, DHashMap f g)
trackM f task = do 
  depsVar <- newMutVar mempty
  result <- bindTask task \key -> do
    value <- fetch key
    g <- f key value
    value <$ atomicModifyMutVar' depsVar \m ->
      (DHM.insert key g m, ())
  (result,) <$> readMutVar depsVar

track
  :: (GHashable f, PrimMonad m)
  => (∀ b. f b -> b -> g b)
  -> TaskT f m a -> TaskT f m (a, DHashMap f g)
track f = trackM \key -> pure . f key

memoise 
  :: (GHashable f, PrimMonad m)
  => MutVar (PrimState m) (DHashMap f (MVar (PrimState m)))
  -> (f ~> TaskT g m) -> f ~> TaskT g m
memoise sv rules key = readMutVar sv >>= \v -> case DHM.lookup key v of
  Just vv -> readMVar vv
  Nothing -> do
    vv <- newEmptyMVar
    join $ atomicModifyMutVar sv \s -> 
      case DHM.alterLookup (Just . fromMaybe vv) key s of
        (Nothing, s') -> (,) s' do
          value <- rules key 
          value <$ putMVar vv value
        (Just vv', _) -> (s, readMVar vv')

newtype Cyclic f = Cyclic (Some f)
  deriving stock (Eq, Ord, Show, Read, Generic, Generic1)
  deriving anyclass (Exception, FTraversable)
  deriving newtype
  ( FFunctor
  , FFoldable
  , FFunctorWithIndex U1
  , FFoldableWithIndex U1
  )

deriving newtype instance Hashable (Some f) => Hashable (Cyclic f)

instance FTraversableWithIndex U1 Cyclic where
  iftraverse f (Cyclic g) = Cyclic <$> iftraverse f g

data MemoEntry s a
  = Started !ThreadId !(MVar s (Maybe a))
  | Done !a

memoiseWithCycleDetection
  :: ∀ f g m. (PrimMonad m, MonadCatch m, Typeable f, GShow f, GHashable f)
  => MutVar (PrimState m) (DHashMap f (MemoEntry (PrimState m)))
  -> MutVar (PrimState m) (HashMap ThreadId ThreadId)
  -> (f ~> TaskT g m) -> f ~> TaskT g m
memoiseWithCycleDetection startedVar depsVar rules = rules' where
  detectCycle threadId deps = go threadId where
    go tid = case HM.lookup tid deps of
      Nothing -> False
      Just dep
        | dep == threadId -> True
        | otherwise -> go dep

  rules' (key :: f a) = readMutVar startedVar >>= \ sm -> case DHM.lookup key sm of
      Just entry -> waitFor entry
      Nothing -> do
        threadId <- unsafeIOToPrim myThreadId
        valueVar <- newEmptyMVar
        join $ atomicModifyMutVar' startedVar \started ->
          case DHM.alterLookup (Just . fromMaybe (Started threadId valueVar)) key started of
            (Just entry, _started') -> (started, waitFor entry)
            (Nothing, started') -> (,) started' $ do -- note `M.catch`
                value <- rules key
                stToPrim do
                  atomicModifyMutVar' startedVar \started'' -> (DHM.insert key (Done value) started'', ())
                  value <$ putMVar valueVar (Just value)
              `M.catch` \(e :: Cyclic f) -> stToPrim do
                atomicModifyMutVar' startedVar \started'' -> (DHM.delete key started'', ())
                putMVar valueVar Nothing
                throwM e
    where
      waitFor = \case
        Done value -> pure value
        Started onThread valueVar -> do
          threadId <- unsafeIOToPrim myThreadId
          join $ atomicModifyMutVar' depsVar \deps ->
            let deps' = HM.insert threadId onThread deps in
            if detectCycle threadId deps' then (,) deps do
              unsafeIOToPrim $ throwIO $ Cyclic $ Some key
            else (,) deps' do
              maybeValue <- readMVar valueVar
              atomicModifyMutVar' depsVar \deps'' -> (HM.delete threadId deps'', ())
              maybe (rules' key) pure maybeValue

data ValueDeps f d a = ValueDeps !a !(DHashMap f d)

pure []

instance (GShow f, Has' Show f d) => Show1 (ValueDeps f d) where
  liftShowsPrec = $(makeLiftShowsPrec ''ValueDeps)

type Traces f d = DHashMap f (ValueDeps f d)

verifyDependencies 
  :: (PrimMonad m, GEq f, Has' Eq f d)
  => (f ~> m)
  -> (∀ b. f b -> b -> m (d b))
  -> ValueDeps f d a 
  -> m (Maybe a)
verifyDependencies f createDependencyRecord (ValueDeps value_ deps) = do
  upToDate <- allM (DHM.toList deps) \(depKey :=> dep) -> do
    depValue <- f depKey
    newDep <- createDependencyRecord depKey depValue
    pure $ eqTagged depKey depKey dep newDep
  pure if upToDate
    then Just value_
    else Nothing
  where
    allM :: Monad m => [a] -> (a -> m Bool) -> m Bool
    allM [] _ = pure True
    allM (x:xs) p = p x >>= \b -> if b
      then allM xs p
      else pure False

record :: GHashable f => f a -> a -> DHashMap f g -> Traces f g -> Traces f g
record k v deps = DHM.insert k $ ValueDeps v deps

data TaskKind = Input | NonInput

data Traced w f a where
  Traced :: f a -> Traced w f (a, w)

instance GEq f => GEq (Traced w f) where
  geq (Traced f) (Traced g) = case geq f g of
    Nothing -> Nothing
    Just Refl -> Just Refl

instance GCompare f => GCompare (Traced w f) where
  gcompare (Traced f) (Traced g) = case gcompare f g of
    GLT -> GLT
    GEQ -> GEQ
    GGT -> GGT

-- | @'tracing' write rules@ runs @write w@ each time a @w@ is returned from a
-- rule in @rules@.
tracing 
  :: ∀ f w g m. Monad m
  => (∀ a. f a -> w -> TaskT g m ())
  -> (Traced w f ~> TaskT g m) -> f ~> TaskT g m
tracing write rules key = do
  (res, w) <- rules $ Traced key
  res <$ write key w

-- | Remember the results of previous @f@ queries and what their dependencies
-- were then.
--
-- If all dependencies of a 'NonInput' query are the same, reuse the old result.
-- 'Input' queries are not reused.
verifyTraces
  :: ∀ f m d. (PrimMonad m, MonadCatch m, GHashable f, Has' Eq f d, Typeable f, GShow f)
  => MutVar (PrimState m) (Traces f d)
  -> (∀ a. f a -> a -> TaskT f m (d a))
  -> (Traced TaskKind f ~> TaskT f m) -> f ~> TaskT f m
verifyTraces tracesVar cdr r key = do
  traces <- readMutVar tracesVar
  maybeValue <- case DHM.lookup key traces of
    Nothing -> pure Nothing
    Just old -> verifyDependencies fetch cdr old `M.catch` \(_ :: Cyclic f) ->
        pure Nothing
  case maybeValue of
    Nothing -> do
      ((value, taskKind), deps) <- trackM cdr $ r $ Traced key
      value <$ case taskKind of
        Input -> pure ()
        NonInput -> atomicModifyMutVar' tracesVar \v -> (record key value deps v, ())
    Just value -> pure value

-- | @'traceFetch' before after rules@ runs @before q@ before a query is
-- performed from @rules@, and @after q result@ every time a query returns with
-- result @result@. 
traceFetch
  :: Monad m
  => (∀ a. f a -> TaskT g m ())
  -> (∀ a. f a -> a -> TaskT g m ())
  -> (f ~> TaskT g m) -> f ~> TaskT g m
traceFetch before after rules key = do
  before key
  result <- rules key
  result <$ after key result

type ReverseDependencies f = HashMap (Some f) (HashSet (Some f))

-- | Write reverse dependencies to the 'IORef.
trackReverseDependencies
  :: (PrimMonad m, GHashable f)
  => MutVar (PrimState m) (ReverseDependencies f)
  -> (f ~> TaskT f m) -> f ~> TaskT f m
trackReverseDependencies reverseDepsVar rules key = do
  (res, deps) <- track (\_ _ -> Const ()) $ rules key
  res <$ unless (DHM.null deps) do
    let newReverseDeps = HM.fromListWith (<>)
          [ (Some depKey, HS.singleton $ Some key)
          | depKey :=> Const () <- DHM.toList deps
          ]
    atomicModifyMutVar' reverseDepsVar \e -> (HM.unionWith (<>) newReverseDeps e, ())

-- | @'reachableReverseDependencies' key@ returns all keys reachable, by
-- reverse dependency, from @key@ from the input 'DHashMap'. It also returns the
-- reverse dependency map with those same keys removed.
reachableReverseDependencies
  :: GHashable f
  => f a
  -> ReverseDependencies f
  -> (DHashMap f (Const ()), ReverseDependencies f)
reachableReverseDependencies key reverseDeps = foldl'
  (\(m', reverseDeps') (Some key') -> first (<> m') $ reachableReverseDependencies key' reverseDeps')
  (DHM.singleton key $ Const (), HM.delete (Some key) reverseDeps)
  (HM.lookupDefault mempty (Some key) reverseDeps)
