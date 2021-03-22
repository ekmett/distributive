{-# Language Trustworthy #-}
{-# options_haddock hide #-}

module Data.Function.Coerce 
( (#.)
, (.#)
, pattern Coerce
, Coe(..)
, runCoe
) where

import Control.Applicative
import Control.Arrow
import Control.Monad.Fix
import Control.Monad.Zip
import Control.Monad.Reader
import Control.Category
import Data.Coerce
import Prelude hiding (id,(.))

(#.) :: Coercible b c => (b -> c) -> (a -> b) -> a -> c
(#.) _ = coerce
{-# inline (#.) #-}

(.#) :: Coercible a b => (b -> c) -> (a -> b) -> a -> c
(.#) f _ = coerce f
{-# inline (.#) #-}

infixr 9 #., .#

pattern Coerce :: Coercible a b => a -> b
pattern Coerce x <- (coerce -> x) where
  Coerce x = coerce x

type role Coe representational representational
data Coe a b where
  Fun :: (a -> b) -> Coe a b
  Coe :: Coercible a b => Coe a b

runCoe :: Coe a b -> a -> b
runCoe (Fun f) = f
runCoe Coe = coerce

instance Functor (Coe a) where
  fmap f = \case
    Coe -> Fun (f . coerce)
    Fun g -> Fun (f . g)
  {-# inline fmap #-}

instance Applicative (Coe a) where
  pure a = Fun \_ -> a
  (<*>) = \f g -> Fun (runCoe f <*> runCoe g)
  (*>) = \_ x -> x
  (<*) = const
  {-# inline pure #-}
  {-# inline (<*>) #-}
  {-# inline (*>) #-}
  {-# inline (<*) #-}

instance Monad (Coe a) where
  (>>=) = \m f -> Fun \a -> runCoe (f (runCoe m a)) a
  {-# inline (>>=) #-}

instance MonadFix (Coe a) where
  mfix = \f -> Fun $ mfix (runCoe . f)
  {-# inline mfix #-}

instance MonadZip (Coe a) where
  mzipWith = liftA2
  {-# inline mzipWith #-}

instance Category Coe where
  id = Coe
  {-# inline id #-}
    
  Fun f . Fun g = Fun (f . g)
  Coe . x = coerce x
  x . Coe = coerce x
  {-# inline (.) #-}
  
instance Arrow Coe where
  arr = Fun
  {-# inline arr #-}

  first = \case
    Coe -> Coe
    Fun f -> Fun (first f)
  {-# inline first #-}

  second = \case
    Coe -> Coe
    Fun f -> Fun (second f)
  {-# inline second #-}

  Coe *** Coe = Coe
  f *** g = Fun (runCoe f *** runCoe g)
  {-# inline (***) #-}

  f &&& g = Fun (runCoe f &&& runCoe g)
  {-# inline (&&&) #-}

instance ArrowLoop Coe where
  loop = \case
    Coe -> Coe
    Fun f -> Fun (loop f)
  {-# inline loop #-}

instance ArrowApply Coe where
  app = Fun (uncurry runCoe)
  {-# inline app #-}

instance ArrowChoice Coe where
  left = \case
    Coe -> Coe
    Fun f -> Fun (left f)
  {-# inline left #-}

  right = \case
    Coe -> Coe
    Fun f -> Fun (right f)
  {-# inline right #-}

  Coe +++ Coe = Coe
  f +++ g = Fun (runCoe f +++ runCoe g)
  {-# inline (+++) #-}

  (|||) = \f g -> Fun (runCoe f ||| runCoe g)
  {-# inline (|||) #-}

instance Semigroup m => Semigroup (Coe a m) where
  (<>) = \f g -> Fun (runCoe f <> runCoe g)
  {-# inline (<>) #-}

instance Monoid m => Monoid (Coe a m) where
  mempty = Fun mempty
  {-# inline mempty #-}

instance MonadReader a (Coe a) where
  reader = Fun
  {-# inline reader #-}
  ask = Coe
  {-# inline ask #-}
  local f g = g . Fun f
  {-# inline local #-}
