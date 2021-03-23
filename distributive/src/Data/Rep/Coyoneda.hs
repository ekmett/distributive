{-# Language Safe #-}

-- |
-- Copyright   : (C) 2021 Edward Kmett, Emily Pillmore
-- License     : BSD-2-Clause OR Apache-2.0
-- Maintainer  : Edward Kmett <ekmett@gmail.com>
-- Stability   : provisional
-- Portability : non-portable

module Data.Rep.Coyoneda
( Coyoneda(CoyonedaDist, Coyoneda)
, liftCoyonedaDist
, liftCoyoneda
, lowerCoyoneda
, hoistCoyoneda
) where

import Control.Applicative
import Control.Monad
import Control.Monad.Fix
import Control.Monad.Zip
import Control.Monad.Trans
import Data.Functor.Classes
import Data.Functor.Compose
import Data.Functor.Identity
import Data.Rep
import Text.Read hiding (lift)

type role Coyoneda representational nominal
data Coyoneda f a where
  CoyonedaDist :: Representable g => g a -> f (Log g) -> Coyoneda f a 

-- I'm not sure whether this pattern can be made work on GHC-8.0,
-- or it's unworkaroundable bug
pattern Coyoneda :: (b -> a) -> f b -> Coyoneda f a
pattern Coyoneda ga flg <- CoyonedaDist (Tabulate ga) flg where
  Coyoneda ga flg = CoyonedaDist ga flg

{-# complete Coyoneda :: Coyoneda #-}

instance (Show1 f, Functor f) => Show1 (Coyoneda f) where
  liftShowsPrec = \ sp sl d (CoyonedaDist f a) ->
    showsUnaryWith (liftShowsPrec sp sl) "liftCoyoneda" d (fmap (index f) a)
  {-# inline liftShowsPrec #-}

instance Read1 f => Read1 (Coyoneda f) where
  liftReadsPrec = \ rp rl -> readsData $
    readsUnaryWith (liftReadsPrec rp rl) "liftCoyoneda" liftCoyoneda
  {-# inline liftReadsPrec #-}

instance Eq1 f => Eq1 (Coyoneda f) where
  liftEq = \eq (CoyonedaDist f xs) (CoyonedaDist g ys) ->
    liftEq (\x y -> eq (index f x) (index g y)) xs ys
  {-# inline liftEq #-}

instance Ord1 f => Ord1 (Coyoneda f) where
  liftCompare = \cmp (CoyonedaDist f xs) (CoyonedaDist g ys) ->
    liftCompare (\x y -> cmp (index f x) (index g y)) xs ys
  {-# inline liftCompare #-}

instance (Functor f, Eq1 f, Eq a) => Eq (Coyoneda f a) where
  (==) = eq1
  {-# inline (==) #-}

instance (Functor f, Ord1 f, Ord a) => Ord (Coyoneda f a) where
  compare = compare1
  {-# inline compare #-}
  
instance (Functor f, Show1 f, Show a) => Show (Coyoneda f a) where
  showsPrec = showsPrec1
  {-# inline showsPrec #-}

instance Read (f a) => Read (Coyoneda f a) where 
  readPrec = parens $ prec 10 $ do
    Ident "liftCoyoneda" <- lexP
    liftCoyoneda <$> step readPrec
  {-# inline readPrec #-}

instance Functor (Coyoneda f) where
  fmap = \f (CoyonedaDist ga fl) -> CoyonedaDist (fmap f ga) fl
  {-# inline fmap #-}

instance Applicative f => Applicative (Coyoneda f) where
  pure = \a -> CoyonedaDist (Identity a) (pure FZ)
  {-# inline pure #-}

  liftA2 = \abc (CoyonedaDist ga flg) (CoyonedaDist hb flh) ->
    CoyonedaDist (Compose $ fmap (\a -> fmap (abc a) hb) ga) (liftA2 (,) flg flh)
  {-# inline liftA2 #-}

  (<*>) = \(CoyonedaDist gab flg) (CoyonedaDist ha flh) ->
    CoyonedaDist (Compose $ fmap (\ab -> fmap ab ha) gab) (liftA2 (,) flg flh)
  {-# inline (<*>) #-}

  (<*) = \(CoyonedaDist ga flg) (CoyonedaDist _ flh) -> CoyonedaDist ga (flg <* flh)
  {-# inline (<*) #-}

  (*>) = \(CoyonedaDist _ flg) (CoyonedaDist ha flh) -> CoyonedaDist ha (flg *> flh)
  {-# inline (*>) #-}

instance Alternative f => Alternative (Coyoneda f) where
  empty = liftCoyoneda empty
  {-# inline empty #-}
  (<|>) = \m n -> liftCoyoneda $ lowerCoyoneda m <|> lowerCoyoneda n
  {-# inline (<|>) #-}

instance MonadIO f => MonadIO (Coyoneda f) where
  liftIO = lift . liftIO
  {-# inline liftIO #-}

instance MonadZip f => MonadZip (Coyoneda f) where
  mzipWith = \abc (CoyonedaDist ga flg) (CoyonedaDist hb flh) ->
    CoyonedaDist (Compose $ fmap (\a -> fmap (abc a) hb) ga) (mzipWith (,) flg flh)
  {-# inline mzipWith #-}

instance Monad f => Monad (Coyoneda f) where
  (>>=) = \(CoyonedaDist f v) k ->
    lift (v >>= lowerCoyoneda . k . index f)
  {-# inline (>>=) #-}

instance MonadFix f => MonadFix (Coyoneda f) where
  mfix = \f -> lift $ mfix (lowerCoyoneda . f)
  {-# INLINE mfix #-}

instance MonadTrans Coyoneda where
  lift = CoyonedaDist id
  {-# inline lift #-}

instance Foldable f => Foldable (Coyoneda f) where
  foldMap = \f (CoyonedaDist (fmap f -> g') flg) -> 
    foldMap (index g') flg
  {-# inline foldMap #-}

instance Traversable f => Traversable (Coyoneda f) where
  traverse = \f (CoyonedaDist (fmap f -> g') flg) -> 
    liftCoyoneda <$> traverse (index g') flg
  {-# inline traverse #-}

instance MonadPlus f => MonadPlus (Coyoneda f) where
  mzero = lift mzero
  {-# inline mzero #-}
  mplus = \m n -> lift $ lowerCoyoneda m `mplus` lowerCoyoneda n
  {-# inline mplus #-}

instance Indexable f => Indexable (Coyoneda f) where
  type Log (Coyoneda f) = Log f
  index = \(CoyonedaDist g flg) lf -> index g (index flg lf)
  {-# inline index #-}

instance Representable f => Representable (Coyoneda f) where
  scatter = \wid2r h2cyf wh -> liftCoyoneda (scatter wid2r (lowerCoyoneda . h2cyf) wh)
  tabulate = \logf2a -> CoyonedaDist (tabulate @f logf2a) askRep
  {-# inline scatter #-}
  {-# inline tabulate #-}

liftCoyonedaDist :: forall g f. Representable g => f (Log g) -> Coyoneda f (Log g)
liftCoyonedaDist = CoyonedaDist (askRep @g)
{-# inline liftCoyonedaDist #-}

liftCoyoneda :: f a -> Coyoneda f a
liftCoyoneda = CoyonedaDist id
{-# inline liftCoyoneda #-}

lowerCoyoneda :: Functor f => Coyoneda f a -> f a
lowerCoyoneda = \(CoyonedaDist f m) -> fmap (index f) m
{-# inline lowerCoyoneda #-}

-- | Lift a natural transformation from @f@ to @g@ to a natural transformation
-- from @Coyoneda f@ to @Coyoneda g@.
hoistCoyoneda :: (forall a. f a -> g a) -> (Coyoneda f b -> Coyoneda g b)
hoistCoyoneda = \f (CoyonedaDist g x) -> CoyonedaDist g (f x)
{-# inline hoistCoyoneda #-}

-- instance ComonadTrans Coyoneda where lower (Coyoneda g fa) = fmap (index g) fa
