{-# LANGUAGE GADTs #-}
{-# Language CPP #-}
{-# Language FlexibleContexts #-}
{-# Language FlexibleInstances #-}
{-# Language MultiParamTypeClasses #-}
{-# Language PatternSynonyms #-}
{-# Language ViewPatterns #-}
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
  , pattern Reader
  , runReader
  -- * Monad Transformer
#if __GLASGOW_HASKELL__ >= 802
  , ReaderT(.., ReaderT, runReaderT)
#else
  , ReaderT(.., ReaderT)
  , runReaderT
#endif
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

pattern Reader :: Distributive f => (Log f -> a) -> Reader f a
#if __GLASGOW_HASKELL__ >= 802

pattern Reader { runReader } <- ReaderDistT (fmap runIdentity . index -> runReader) where
  Reader f = ReaderDistT (tabulate (coerce f))

#else

pattern Reader f <- ReaderDistT (fmap runIdentity . index -> f) where
  Reader f = ReaderDistT (tabulate (coerce f))

runReader :: Distributive f => Reader f a -> Log f -> a
runReader = fmap runIdentity . runReaderT
#endif

-- | This 'representable monad transformer' transforms any monad @m@ with a 'Distributive' 'Monad'.
-- This monad in turn is also representable if @m@ is 'Distributive'.
newtype ReaderT f m b = ReaderDistT { runReaderDistT :: f (m b) }

pattern ReaderT :: Distributive f => (Log f -> m a) -> ReaderT f m a
#if __GLASGOW_HASKELL__ >= 802

pattern ReaderT { runReaderT } <- ReaderDistT (index -> runReaderT) where
  ReaderT f = ReaderDistT (tabulate f)

#else
pattern ReaderT f <- (runReaderT -> f) where
  ReaderT f = ReaderDistT (tabulate f)

runReaderT :: Distributive f => ReaderT f m b -> Log f -> m b
runReaderT = index .# runReaderDistT
#endif

instance (Functor f, Functor m) => Functor (ReaderT f m) where
  fmap f = ReaderDistT #. fmap (fmap f) .# runReaderDistT

instance (Distributive f, Distributive m) => Distributive (ReaderT f m) where
  type Log (ReaderT f m) = (Log f, Log m)
  scatter k f = coerce $ scatter k ((Comp1 . runReaderDistT) #. f)
  index (ReaderDistT f) (x, y) = index (index f x) y
  tabulate f = ReaderDistT $ tabulate $ \i -> tabulate $ \j -> f (i, j)
  {-# inline tabulate #-}
  {-# inline index #-}

instance (Distributive f, Applicative m) => Applicative (ReaderT f m) where
  pure = ReaderDistT #. (pureDist . pure)
  ReaderDistT ff <*> ReaderDistT fa = ReaderDistT $ liftD2 (<*>) ff fa
  ReaderDistT fa *> ReaderDistT fb = ReaderDistT $ liftD2 (*>) fa fb
  ReaderDistT fa <* ReaderDistT fb = ReaderDistT $ liftD2 (<*) fa fb

instance (Distributive f, Monad m) => Monad (ReaderT f m) where
  ReaderDistT fm >>= f = ReaderDistT $ liftD2 (>>=) fm $ distribute (runReaderDistT . f)

instance (Distributive f, Monad m, Log f ~ e) => MonadReader e (ReaderT f m) where
  ask = ReaderDistT $ tabulate pure
  local f m = ReaderT $ \r -> runReaderT m (f r)
  reader = ReaderT . fmap pure

instance Distributive f => MonadTrans (ReaderT f) where
  lift = ReaderDistT #. pureDist

instance (Distributive f, MonadIO m) => MonadIO (ReaderT f m) where
  liftIO = lift . liftIO

instance (Distributive f, MonadWriter w m) => MonadWriter w (ReaderT f m) where
  tell = lift . tell
  listen = ReaderDistT #. fmap listen .# runReaderDistT
  pass = ReaderDistT #. fmap pass .# runReaderDistT

instance (Foldable f, Foldable m) => Foldable (ReaderT f m) where
  foldMap f = foldMap (foldMap f) .# runReaderDistT

instance (Traversable f, Traversable m) => Traversable (ReaderT f m) where
  traverse f = fmap ReaderDistT . traverse (traverse f) .# runReaderDistT
