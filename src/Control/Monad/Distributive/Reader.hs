{-# LANGUAGE GADTs #-}
{-# Language CPP #-}
{-# Language FlexibleContexts #-}
{-# Language FlexibleInstances #-}
{-# Language MultiParamTypeClasses #-}
{-# Language TypeFamilies #-}
{-# Language TypeOperators #-}
{-# Language TypeSynonymInstances #-}
{-# Language UndecidableInstances #-}
{-# OPTIONS_GHC -fenable-rewrite-rules -fno-warn-orphans #-}
----------------------------------------------------------------------
-- |
-- Module      :  Control.Monad.Distributive.Reader
-- Copyright   :  (c) Edward Kmett 2011-2021,
--                (c) Conal Elliott 2008
-- License     :  BSD3
--
-- Maintainer  :  ekmett@gmail.com
-- Stability   :  experimental
--
-- Distributive functors on Hask are all monads, because they are isomorphic to
-- a 'Reader' monad.
----------------------------------------------------------------------

module Control.Monad.Distributive.Reader
  (
  -- * Distributive functor monad
    Reader
  , runReader
  -- * Monad Transformer
  , ReaderT(..), readerT, runReaderT
  , MonadReader(..)
) where

import Control.Monad.Reader.Class
import Control.Monad.Writer.Class as Writer
import Control.Monad.Trans.Class
import Control.Monad.IO.Class
import Data.Coerce
import Data.Distributive
import Data.Distributive.Util
import Data.Functor.Identity
import GHC.Generics

type Reader f = ReaderT f Identity

runReader :: Distributive f => Reader f b -> Log f -> b
runReader = fmap runIdentity . runReaderT

-- | This 'representable monad transformer' transforms any monad @m@ with a 'Distributive' 'Monad'.
-- This monad in turn is also representable if @m@ is 'Distributive'.
newtype ReaderT f m b = ReaderT { getReaderT :: f (m b) }

readerT :: Distributive f => (Log f -> m b) -> ReaderT f m b
readerT = ReaderT #. tabulate

runReaderT :: Distributive f => ReaderT f m b -> Log f -> m b
runReaderT = index .# getReaderT

instance (Functor f, Functor m) => Functor (ReaderT f m) where
  fmap f = ReaderT #. fmap (fmap f) .# getReaderT

instance (Distributive f, Distributive m) => Distributive (ReaderT f m) where
  type Log (ReaderT f m) = (Log f, Log m)
  scatter k f = coerce $ scatter k ((Comp1 . getReaderT) #. f)
  index (ReaderT f) (x, y) = index (index f x) y
  tabulate f = ReaderT $ tabulate $ \i -> tabulate $ \j -> f (i, j)
  {-# inline tabulate #-}
  {-# inline index #-}

instance (Distributive f, Applicative m) => Applicative (ReaderT f m) where
  pure = ReaderT #. (pureDist . pure)
  ReaderT ff <*> ReaderT fa = ReaderT $ liftD2 (<*>) ff fa
  ReaderT fa *> ReaderT fb = ReaderT $ liftD2 (*>) fa fb
  ReaderT fa <* ReaderT fb = ReaderT $ liftD2 (<*) fa fb

instance (Distributive f, Monad m) => Monad (ReaderT f m) where
  ReaderT fm >>= f = ReaderT $ liftD2 (>>=) fm $ distribute (getReaderT . f)

instance (Distributive f, Monad m, Log f ~ e) => MonadReader e (ReaderT f m) where
  ask = ReaderT $ tabulate pure
  local f m = readerT $ \r -> runReaderT m (f r)
  reader = readerT . fmap return

instance Distributive f => MonadTrans (ReaderT f) where
  lift = ReaderT #. pureDist

instance (Distributive f, MonadIO m) => MonadIO (ReaderT f m) where
  liftIO = lift . liftIO

instance (Distributive f, MonadWriter w m) => MonadWriter w (ReaderT f m) where
  tell = lift . tell
  listen = ReaderT #. fmap listen .# getReaderT
  pass = ReaderT #. fmap pass .# getReaderT

instance (Foldable f, Foldable m) => Foldable (ReaderT f m) where
  foldMap f = foldMap (foldMap f) .# getReaderT

instance (Traversable f, Traversable m) => Traversable (ReaderT f m) where
  traverse f = fmap ReaderT . traverse (traverse f) .# getReaderT
