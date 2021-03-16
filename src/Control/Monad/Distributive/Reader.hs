{-# LANGUAGE GADTs #-}
{-# Language CPP #-}
{-# Language FlexibleContexts #-}
{-# Language FlexibleInstances #-}
{-# Language MultiParamTypeClasses #-}
{-# Language PatternSynonyms #-}
{-# Language RoleAnnotations #-}
{-# Language Trustworthy #-}
{-# Language TypeFamilies #-}
{-# Language TypeOperators #-}
{-# Language ScopedTypeVariables #-}
{-# Language TypeSynonymInstances #-}
{-# Language UndecidableInstances #-}
{-# Language ViewPatterns #-}
{-# OPTIONS_GHC -fenable-rewrite-rules -fno-warn-orphans #-}

#ifndef MIN_VERSION_base
#define MIN_VERSION_base(_x,_y,_z) 1
#endif
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
, ReaderT(.., ReaderT, runReaderT)
, liftCatch
, liftCallCC
) where

import Control.Applicative
import Control.Monad
import Control.Monad.Cont.Class
import Control.Monad.Error.Class
import Control.Monad.Fail
import Control.Monad.Fix
import Control.Monad.Zip
import Control.Monad.IO.Class
import Control.Monad.Reader.Class
import Control.Monad.Signatures
import Control.Monad.State.Class
import Control.Monad.Trans.Class
import Control.Monad.Writer.Class as Writer
import Data.Coerce
import Data.Distributive
import Data.Distributive.Coerce
import Data.Functor.Contravariant
import Data.Functor.Identity
import Data.HKD
import GHC.Generics

type Reader f = ReaderT f Identity

pattern Reader :: Distributive f => (Log f -> a) -> Reader f a
pattern Reader { runReader } <- ReaderT (Coerce runReader)

{-# complete Reader #-}

-- | This 'representable monad transformer' transforms any monad @m@ with a 'Distributive' 'Monad'.
-- This monad in turn is also representable if @m@ is 'Distributive'.
type role ReaderT representational nominal nominal
newtype ReaderT f m b = ReaderDistT { runReaderDistT :: f (m b) }

pattern ReaderT :: Distributive f => (Log f -> m a) -> ReaderT f m a
pattern ReaderT { runReaderT } = ReaderDistT (Tabulate runReaderT)

{-# complete ReaderT #-}

instance (Functor f, Functor m) => Functor (ReaderT f m) where
  fmap = \f -> ReaderDistT #. fmap (fmap f) .# runReaderDistT

instance (Distributive f, Distributive m) => Distributive (ReaderT f m) where
  type Log (ReaderT f m) = (Log f, Log m)
  scatter = \k f -> coerce $ scatter k ((Comp1 . runReaderDistT) #. f)
  index = \(ReaderDistT f) (x, y) -> index (index f x) y
  tabulate = \f -> ReaderDistT $ tabulate $ \i -> tabulate $ \j -> f (i, j)
  {-# inline tabulate #-}
  {-# inline index #-}

instance (Distributive f, Applicative m) => Applicative (ReaderT f m) where
  pure = ReaderDistT #. (pureDist . pure)
  {-# inline pure #-}
  (<*>) = \(ReaderDistT ff) (ReaderDistT fa) -> ReaderDistT $ liftD2 (<*>) ff fa
  {-# inline (<*>) #-}
  (*>) = \(ReaderDistT fa) (ReaderDistT fb) -> ReaderDistT $ liftD2 (*>) fa fb
  {-# inline (*>) #-}
  (<*) = \(ReaderDistT fa) (ReaderDistT fb) -> ReaderDistT $ liftD2 (<*) fa fb
  {-# inline (<*) #-}

instance (Distributive f, Monad m) => Monad (ReaderT f m) where
  (>>=) = \(ReaderDistT fm) f ->
    ReaderDistT $ liftD2 (>>=) fm $ distribute (runReaderDistT . f)
  {-# inline (>>=) #-}
#if !(MIN_VERSION_base(4,13,0))
  fail = lift . Control.Monad.fail
  {-# inline fail #-}
#endif

instance (Distributive f, MonadFail m) => MonadFail (ReaderT f m) where
  fail = lift . Control.Monad.Fail.fail
  {-# inline fail #-}

instance (Distributive f, Monad m, Log f ~ e) => MonadReader e (ReaderT f m) where
  ask = ReaderDistT $ tabulate pure
  {-# inline ask #-}
  local = \f m -> ReaderT $ \r -> runReaderT m (f r)
  {-# inline local #-}
  reader = ReaderT . fmap pure
  {-# inline reader #-}

instance Distributive f => MonadTrans (ReaderT f) where
  lift = ReaderDistT #. pureDist
  {-# inline lift #-}

liftReaderT :: Distributive f => m a -> ReaderT f m a
liftReaderT = ReaderDistT #. pureDist
{-# inline liftReaderT #-}

instance (Distributive f, MonadIO m) => MonadIO (ReaderT f m) where
  liftIO = lift . liftIO
  {-# inline liftIO #-}

instance (Distributive f, MonadWriter w m) => MonadWriter w (ReaderT f m) where
  tell = lift . tell
  {-# inline tell #-}
  listen = ReaderDistT #. fmap listen .# runReaderDistT
  {-# inline listen #-}
  pass = ReaderDistT #. fmap pass .# runReaderDistT
  {-# inline pass #-}

instance (Foldable f, Foldable m) => Foldable (ReaderT f m) where
  foldMap f = foldMap (foldMap f) .# runReaderDistT
  {-# inline foldMap #-}

instance (Traversable f, Traversable m) => Traversable (ReaderT f m) where
  traverse f = fmap ReaderDistT . traverse (traverse f) .# runReaderDistT
  {-# inline traverse #-}

instance (Distributive f, MonadState s m) => MonadState s (ReaderT f m) where
  get = lift get
  {-# inline get #-}
  put = lift . put
  {-# inline put #-}
  state = lift . state
  {-# inline state #-}

instance (Distributive f, MonadError e m) => MonadError e (ReaderT f m) where
  throwError = lift . throwError
  {-# inline throwError #-}
  catchError = liftCatch catchError
  {-# inline catchError #-}

data DCatch x e m f = DCatch (ReaderT f m x) (e -> ReaderT f m x)

withReaderDistT :: (f (m a) -> g (n b)) -> ReaderT f m a -> ReaderT g n b
withReaderDistT f = ReaderDistT #. f .# runReaderDistT

instance FFunctor (DCatch x y m) where
  ffmap f (DCatch l r) = DCatch (withReaderDistT f l) (withReaderDistT f . r)
  {-# inline ffmap #-}

-- | Lift a @catchE@ operation to the new monad.
liftCatch :: Distributive f => Catch e m a -> Catch e (ReaderT f m) a
-- liftCatch = \f m h -> ReaderT $ \ r -> f (runReaderT m r) (\ e -> runReaderT (h e) r)
liftCatch = \ f m h ->
  ReaderDistT $ distrib (DCatch m h) $ \(DCatch m' h') -> coerce f m' h'
{-# inline liftCatch #-}

newtype DCompReaderT g m a f = DCompReaderT (g (ReaderT f m a))

instance Functor g => FFunctor (DCompReaderT g m a) where
  ffmap f (DCompReaderT k) = DCompReaderT (fmap (withReaderDistT f) k)
  {-# inline ffmap #-}

-- | Lift a @callCC@ operation to the new monad.
liftCallCC :: forall f m a b. Distributive f => CallCC m a b -> CallCC (ReaderT f m) a b
liftCallCC = \callCC' f ->
  ReaderDistT $ distrib (DCompReaderT f) $ \(DCompReaderT f') ->
    callCC' $ \c -> coerce $ f' (ReaderDistT #. pureDist . c)
--liftCallCC = \callCC' f -> ReaderT $ \r ->
--  callCC' $ \c -> runReaderT (f (ReaderDistT #. pureDist . c)) r
{-# inline liftCallCC #-}

instance (Distributive f, MonadCont m) => MonadCont (ReaderT f m) where
  callCC = liftCallCC callCC
  {-# inline callCC #-}

instance (Distributive f, Alternative m) => Alternative (ReaderT f m) where
  empty = liftReaderT empty
  {-# inline empty #-}
  (<|>) = \(ReaderDistT fm) -> ReaderDistT #. liftD2 (<|>) fm .# runReaderDistT
  {-# inline (<|>) #-}

instance (Distributive f, MonadPlus m) => MonadPlus (ReaderT f m)

instance (Distributive f, MonadFix m) => MonadFix (ReaderT f m) where
  mfix = \f -> ReaderDistT $ distrib (DCompReaderT f) $ mfix . coerce
  {-# inline mfix #-}

instance (Distributive f, MonadZip m) => MonadZip (ReaderT f m) where
  mzipWith = \f (ReaderDistT m) -> ReaderDistT #. liftD2 (mzipWith f) m .# runReaderDistT
  {-# inline mzipWith #-}

instance (Distributive f, Contravariant m) => Contravariant (ReaderT f m) where
  contramap = \f -> ReaderDistT #. fmap (contramap f) .# runReaderDistT
  {-# INLINE contramap #-}
