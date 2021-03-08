{-# LANGUAGE GADTs, TypeFamilies, TypeOperators, CPP, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, UndecidableInstances, TypeSynonymInstances #-}
{-# OPTIONS_GHC -fenable-rewrite-rules -fno-warn-orphans #-}
----------------------------------------------------------------------
-- |
-- Module      :  Control.Monad.Representable.Reader
-- Copyright   :  (c) Edward Kmett 2011,
--                (c) Conal Elliott 2008
-- License     :  BSD3
--
-- Maintainer  :  ekmett@gmail.com
-- Stability   :  experimental
--
-- Distributive functors on Hask are all monads, because they are isomorphic to
-- a 'Reader' monad.
----------------------------------------------------------------------

module Control.Monad.Representable.Reader
  (
  -- * Distributive functor monad
    Reader
  , runReader
  -- * Monad Transformer
  , ReaderT(..), readerT, runReaderT
  , MonadReader(..)
) where

#if __GLASGOW_HASKELL__ < 710
import Control.Applicative
#endif
-- import Control.Comonad
import Control.Monad.Reader.Class
import Control.Monad.Writer.Class as Writer
import Control.Monad.Trans.Class
import Control.Monad.IO.Class
import Data.Distributive
#if __GLASGOW_HASKELL__ < 710
import Data.Foldable
#endif
-- import Data.Functor.Bind
-- import Data.Functor.Extend
import Data.Functor.Identity
import Data.Distributive
#if __GLASGOW_HASKELL__ < 710
import Data.Traversable
#endif
#if !(MIN_VERSION_base(4,11,0))
import Data.Semigroup
#endif
-- import Data.Semigroup.Foldable
-- import Data.Semigroup.Traversable
import GHC.Generics hiding (Rep)

type Reader f = ReaderT f Identity

runReader :: Distributive f => Reader f b -> Log f -> b
runReader = fmap runIdentity . runReaderT

-- * This 'representable monad transformer' transforms any monad @m@ with a 'Representable' 'Monad'.
--   This monad in turn is also representable if @m@ is 'Representable'.
newtype ReaderT f m b = ReaderT { getReaderT :: f (m b) }

readerT :: Distributive f => (Log f -> m b) -> ReaderT f m b
readerT = ReaderT . tabulate

runReaderT :: Distributive f => ReaderT f m b -> Log f -> m b
runReaderT = index . getReaderT

instance (Functor f, Functor m) => Functor (ReaderT f m) where
  fmap f = ReaderT . fmap (fmap f) . getReaderT

instance (Distributive f, Distributive m) => Distributive (ReaderT f m) where
  type Log (ReaderT f m) = (Log f, Log m)
  tabulate = ReaderT . tabulate . fmap tabulate . curry
  index = uncurry . fmap index . index . getReaderT

  scatter k phi wg = error "TODO: copy me from :.:"

-- TODO: move to semigroupoids
-- instance (Distributive f, Apply m) => Apply (ReaderT f m) where
--   ReaderT ff <.> ReaderT fa = ReaderT (unCo ((<.>) <$> Co ff <.> Co fa))

instance (Distributive f, Applicative m) => Applicative (ReaderT f m) where
  pure = ReaderT . pureDist . pure
  ReaderT ff <*> ReaderT fa = ReaderT (liftD2 (<*>) ff fa)

-- TODO: move to semigroupoids
-- instance (Distributive f, Bind m) => Bind (ReaderT f m) where
--   ReaderT fm >>- f = ReaderT $ mzipWithRep (>>-) fm $ distribute (getReaderT . f)

instance (Distributive f, Monad m) => Monad (ReaderT f m) where
#if __GLASGOW_HASKELL__ < 710
  return = ReaderT . pureRep . return
#endif
  ReaderT fm >>= f = ReaderT $ liftD2 (>>=) fm $ distribute (getReaderT . f)

#if __GLASGOW_HASKELL >= 704

instance (Distributive f, Monad m, Rep f ~ e) => MonadReader e (ReaderT f m) where
  ask = ReaderT (tabulate return)
  local f m = readerT $ \r -> runReaderT m (f r)
#if MIN_VERSION_transformers(0,3,0)
  reader = readerT . fmap return
#endif

#endif

-- TODO: could there be (Functor f, Represesentable g, MonadFree f m) => MonadFree f (ReaderT g m) ?

instance Distributive f => MonadTrans (ReaderT f) where
  lift = ReaderT . pureDist

-- TODO: move to comonad
-- instance (Distributive f, Representable m, Semigroup (Rep f), Semigroup (Rep m)) => Extend (ReaderT f m) where
--   extended = extendedRep
--   duplicated = duplicatedRep
-- 
-- instance (Distributive f, Representable m, Monoid (Rep f), Monoid (Rep m)) => Comonad (ReaderT f m) where
--   extend = extendRep
--   duplicate = duplicateRep
--   extract = extractRep

instance (Distributive f, MonadIO m) => MonadIO (ReaderT f m) where
  liftIO = lift . liftIO

instance (Distributive f, MonadWriter w m) => MonadWriter w (ReaderT f m) where
  tell = lift . tell
  listen = ReaderT . fmap listen . getReaderT
  pass = ReaderT . fmap pass . getReaderT

-- misc. instances that can exist, but aren't particularly about representability

instance (Foldable f, Foldable m) => Foldable (ReaderT f m) where
  foldMap f = foldMap (foldMap f) . getReaderT


instance (Traversable f, Traversable m) => Traversable (ReaderT f m) where
  traverse f = fmap ReaderT . traverse (traverse f) . getReaderT

-- move to semigroupoids
-- instance (Foldable1 f, Foldable1 m) => Foldable1 (ReaderT f m) where
--   foldMap1 f = foldMap1 (foldMap1 f) . getReaderT
-- 
-- instance (Traversable1 f, Traversable1 m) => Traversable1 (ReaderT f m) where
--   traverse1 f = fmap ReaderT . traverse1 (traverse1 f) . getReaderT
