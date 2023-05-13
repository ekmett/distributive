{-# Language CPP #-}
{-# Language Trustworthy #-}

-- |
-- Copyright   : (c) Edward Kmett 2011-2021,
--               (c) Conal Elliott 2008
-- License     : BSD-2-Clause OR Apache-2.0
-- Maintainer  : Edward Kmett <ekmett@gmail.com>
-- Stability   : experimental
-- Portability : non-portable
--
-- A 'ReaderT' monad that uses a 'Representable' functor instead
-- of a function.

module Control.Monad.Rep.Reader
(
-- * Representable functor monad
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
import Data.Data
import Data.Function.Coerce
import Data.Functor.Contravariant
import Data.Functor.Identity
import Data.Rep
import Data.HKD
import GHC.Generics

type Reader f = ReaderT f Identity

pattern Reader :: Representable f => (Log f -> a) -> Reader f a
pattern Reader { runReader } <- ReaderT (Coerce runReader)

{-# complete Reader #-}

-- | This 'representable monad transformer' transforms any monad @m@ with a 'Representable' 'Monad'.
-- This monad in turn is also representable if @m@ is 'Representable'.
type role ReaderT representational nominal nominal
newtype ReaderT f m b = ReaderRepT { runReaderRepT :: f (m b) }
  deriving (Generic, Generic1, Data)

pattern ReaderT :: Representable f => (Log f -> m a) -> ReaderT f m a
pattern ReaderT { runReaderT } = ReaderRepT (Tabulate runReaderT)
{-# complete ReaderT #-}

instance (Functor f, Functor m) => Functor (ReaderT f m) where
  fmap = \f -> ReaderRepT #. fmap (fmap f) .# runReaderRepT

instance (Indexable f, Indexable m) => Indexable (ReaderT f m) where
  type Log (ReaderT f m) = (Log f, Log m)
  index = \(ReaderRepT f) (x, y) -> index (index f x) y
  {-# inline index #-}

instance (Representable f, Representable m) => Representable (ReaderT f m) where
  scatter = \k f -> coerce $ scatter k ((Comp1 . runReaderRepT) #. f)
  tabulate = \f -> ReaderRepT $ tabulate \i -> tabulate \j -> f (i, j)
  {-# inline tabulate #-}

instance (Representable f, Applicative m) => Applicative (ReaderT f m) where
  pure = ReaderRepT #. (pureRep . pure)
  {-# inline pure #-}
  (<*>) = \(ReaderRepT ff) (ReaderRepT fa) -> ReaderRepT $ liftR2 (<*>) ff fa
  {-# inline (<*>) #-}
  (*>) = \(ReaderRepT fa) (ReaderRepT fb) -> ReaderRepT $ liftR2 (*>) fa fb
  {-# inline (*>) #-}
  (<*) = \(ReaderRepT fa) (ReaderRepT fb) -> ReaderRepT $ liftR2 (<*) fa fb
  {-# inline (<*) #-}

instance (Representable f, Monad m) => Monad (ReaderT f m) where
  (>>=) = \(ReaderRepT fm) f ->
    ReaderRepT $ liftR2 (>>=) fm $ distribute (runReaderRepT . f)
  {-# inline (>>=) #-}
#if !(MIN_VERSION_base(4,13,0))
  fail = lift . Control.Monad.fail
  {-# inline fail #-}
#endif

instance (Representable f, MonadFail m) => MonadFail (ReaderT f m) where
  fail = lift . Control.Monad.Fail.fail
  {-# inline fail #-}

instance (Representable f, Monad m, Log f ~ e) => MonadReader e (ReaderT f m) where
  ask = ReaderRepT $ tabulate pure
  {-# inline ask #-}
  local = \f m -> ReaderT \r -> runReaderT m (f r)
  {-# inline local #-}
  reader = ReaderT . fmap pure
  {-# inline reader #-}

instance Representable f => MonadTrans (ReaderT f) where
  lift = ReaderRepT #. pureRep
  {-# inline lift #-}

liftReaderT :: Representable f => m a -> ReaderT f m a
liftReaderT = ReaderRepT #. pureRep
{-# inline liftReaderT #-}

instance (Representable f, MonadIO m) => MonadIO (ReaderT f m) where
  liftIO = lift . liftIO
  {-# inline liftIO #-}

instance (Representable f, MonadWriter w m) => MonadWriter w (ReaderT f m) where
  tell = lift . tell
  {-# inline tell #-}
  listen = ReaderRepT #. fmap listen .# runReaderRepT
  {-# inline listen #-}
  pass = ReaderRepT #. fmap pass .# runReaderRepT
  {-# inline pass #-}

instance (Foldable f, Foldable m) => Foldable (ReaderT f m) where
  foldMap f = foldMap (foldMap f) .# runReaderRepT
  {-# inline foldMap #-}

instance (Traversable f, Traversable m) => Traversable (ReaderT f m) where
  traverse f = fmap ReaderRepT . traverse (traverse f) .# runReaderRepT
  {-# inline traverse #-}

instance (Representable f, MonadState s m) => MonadState s (ReaderT f m) where
  get = lift get
  {-# inline get #-}
  put = lift . put
  {-# inline put #-}
  state = lift . state
  {-# inline state #-}

instance (Representable f, MonadError e m) => MonadError e (ReaderT f m) where
  throwError = lift . throwError
  {-# inline throwError #-}
  catchError = liftCatch catchError
  {-# inline catchError #-}

data DCatch x e m f = DCatch (ReaderT f m x) (e -> ReaderT f m x)

withReaderRepT :: (f (m a) -> g (n b)) -> ReaderT f m a -> ReaderT g n b
withReaderRepT f = ReaderRepT #. f .# runReaderRepT

instance FFunctor (DCatch x y m) where
  ffmap f (DCatch l r) = DCatch (withReaderRepT f l) (withReaderRepT f . r)
  {-# inline ffmap #-}

-- | Lift a @catchE@ operation to the new monad.
liftCatch :: Representable f => Catch e m a -> Catch e (ReaderT f m) a
-- liftCatch = \f m h -> ReaderT \ r -> f (runReaderT m r) (\ e -> runReaderT (h e) r)
liftCatch = \ f m h ->
  ReaderRepT $ distrib (DCatch m h) \(DCatch m' h') -> coerce f m' h'
{-# inline liftCatch #-}

newtype DCompReaderT g m a f = DCompReaderT (g (ReaderT f m a))

instance Functor g => FFunctor (DCompReaderT g m a) where
  ffmap f (DCompReaderT k) = DCompReaderT (fmap (withReaderRepT f) k)
  {-# inline ffmap #-}

-- | Lift a @callCC@ operation to the new monad.
liftCallCC :: forall f m a b. Representable f => CallCC m a b -> CallCC (ReaderT f m) a b
liftCallCC = \callCC' f ->
  ReaderRepT $ distrib (DCompReaderT f) \(DCompReaderT f') ->
    callCC' \c -> coerce $ f' (ReaderRepT #. pureRep . c)
{-# inline liftCallCC #-}

instance (Representable f, MonadCont m) => MonadCont (ReaderT f m) where
  callCC = liftCallCC callCC
  {-# inline callCC #-}

instance (Representable f, Alternative m) => Alternative (ReaderT f m) where
  empty = liftReaderT empty
  {-# inline empty #-}
  (<|>) = \(ReaderRepT fm) -> ReaderRepT #. liftR2 (<|>) fm .# runReaderRepT
  {-# inline (<|>) #-}

instance (Representable f, MonadPlus m) => MonadPlus (ReaderT f m)

instance (Representable f, MonadFix m) => MonadFix (ReaderT f m) where
  mfix = \f -> ReaderRepT $ distrib (DCompReaderT f) $ mfix . coerce
  {-# inline mfix #-}

instance (Representable f, MonadZip m) => MonadZip (ReaderT f m) where
  mzipWith = \f (ReaderRepT m) -> ReaderRepT #. liftR2 (mzipWith f) m .# runReaderRepT
  {-# inline mzipWith #-}

instance (Representable f, Contravariant m) => Contravariant (ReaderT f m) where
  contramap = \f -> ReaderRepT #. fmap (contramap f) .# runReaderRepT
  {-# INLINE contramap #-}
