{-# Language CPP #-}
{-# Language DerivingStrategies #-}
{-# Language DeriveGeneric #-}
{-# Language GADTs #-}
{-# Language TypeFamilies #-}
{-# Language DeriveFunctor #-}
{-# Language Safe #-}
#if __GLASGOW_HASKELL__ >= 806
{-# Language DerivingVia #-}
#endif
-- |
-- Copyright   :  (C) 2012-2021 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  portable
--
-- <http://en.wikipedia.org/wiki/Moore_machine>

module Data.Machine.Distributive.Moore
( Moore(..)
, logMoore
, unfoldMoore
, wrapMoore
) where

import Control.Applicative
import Control.Monad.Fix
import Control.Monad.Zip
import Control.Monad.Reader.Class
import Data.Distributive
import Data.Distributive.Endo
--import Data.Semigroup
--import Data.Monoid
import GHC.Generics
import Prelude

-- type role Moore representational representational
data Moore a b where
    Moore :: Distributive f => f b -> (a -> Endo f) -> Log f -> Moore a b
  deriving (Monad, MonadFix, MonadReader [a]) via (Dist (Moore a)

instance Functor (Moore a) where
  fmap f (Moore k g s) = Moore (fmap f k) g s
  a <$ _ = Moore (Identity a) (\_ -> Identity ()) ()

instance Distributive (Moore a) where
  type Log (Moore a) = [a]
  index (Moore k g s0) = k . foldl (\s a -> appEndo (g a) s) s0
  tabulate f = Moore f (Endo . (:)) []
  scatter = scatterRep

instance Applicative (Moore a) where
  pure a = Moore (Identity a) (\_ -> Identity ()) ()
  {-# inline pure #-}
  Moore kf gf zf <*> Moore ka ga za = Moore
    (Compose $ (<$> ka) <$> kf)
    (\a -> let EndoDist x = gf a
               EndoDist y = ga a
           in  EndoDist (Compose $ (\lx -> ((,) lx) <$> y) <$> x))
    (zf, za)
  liftA2 f (Moore ka ga za) (Moore kb gb zb) = Moore
    (Compose $ (\a -> (f a <$> kb)) <$> ka)
    (\i -> let EndoDist x = ga i
               EndoDist y = gb i
           in  EndoDist (Compose $ (\lx -> ((,) lx) <$> y) <$> x))
    (za, zb)
  {-# inline liftA2 #-}
  _ *> m = m
  {-# inline (*>) #-}
  m <* _ = m
  {-# inline (<*) #-}

instance MonadZip (Moore a) where
  mzipWith = liftA2
  {-# inline mzipWith #-}

wrapMoore :: b -> (a -> Moore a b) -> Moore a b
wrapMoore first step1 = Moore (maybe first (\(Moore k _ s) -> k s)) step Nothing where
  step a = Endo $ \s -> Just $ case s of
    Nothing -> step1 a
    Moore k g z -> Moore k g $ appEndo (g a) z


#if __GLASGOW_HASKELL__ < 806
instance Monad (Moore a) where
  (>>=) = bindDist
  {-# inline (>>=) #-}
  (>>) = (*>)
  {-# inline (>>) #-}

instance MonadReader (Moore a) where
  ask = askDist
  {-# inline ask #-}
  local = localDist
  {-# inline local #-}

instance MonadFix (Moore a) where
  mfix = mfixDist
  {-# inline mfix #-}
#endif

-- | Accumulate the input as a sequence.
logMoore :: Monoid m => Moore m m
logMoore = Moore id mappend mempty
{-# INLINE logMoore #-}

-- | Construct a Moore machine from a state valuation and transition function
unfoldMoore :: (s -> b) -> (s -> a -> s) -> s -> Moore a b
unfoldMoore = Moore
{-# INLINE unfoldMoore #-}

instance MonadReader [a] (Moore a) where

instance Semigroup b => Semigroup (Moore a b) where
  Moore x f <> Moore y g = Moore (x <> y) (f <> g)
  {-# inline (<>) #-}

instance Monoid b => Monoid (Moore a b) where
  mempty = Moore mempty mempty
  {-# inline mempty #-}
#if !(MIN_VERSION_base(4,11,0))
  Moore x f `mappend` Moore y g = Moore (x `mappend` y) (f `mappend` g)
  {-# inline mappend #-}
#endif

instance Num b => Num (Moore a b) where
  (+) = liftA2 (+)
  (-) = liftA2 (-)
  (*) = liftA2 (*)
  negate = fmap negate
  abs = fmap abs
  signum = fmap signum
  fromInteger = pure . fromInteger
  {-# inline (+) #-}
  {-# inline (-) #-}
  {-# inline (*) #-}
  {-# inline negate #-}
  {-# inline abs #-}
  {-# inline signum #-}
  {-# inline fromInteger #-}

instance Fractional b => Fractional (Moore a b) where
  (/) = liftA2 (/)
  recip = fmap recip
  fromRational = pure . fromRational
  {-# inline (/) #-}
  {-# inline recip #-}
  {-# inline fromRational #-}

instance Floating b => Floating (Moore a b) where
  pi = pure pi
  exp = fmap exp
  log = fmap log
  sqrt = fmap sqrt
  (**) = liftA2 (**)
  logBase = liftA2 logBase
  sin = fmap sin
  cos = fmap cos
  tan = fmap tan
  asin = fmap asin
  acos = fmap acos
  atan = fmap atan
  sinh = fmap sinh
  cosh = fmap cosh
  tanh = fmap tanh
  asinh = fmap asinh
  acosh = fmap acosh
  atanh = fmap atanh
  log1p = fmap log1p
  expm1 = fmap expm1
  log1pexp = fmap log1pexp
  log1mexp = fmap log1mexp
  {-# inline pi #-}
  {-# inline exp #-}
  {-# inline log #-}
  {-# inline sqrt #-}
  {-# inline (**) #-}
  {-# inline logBase #-}
  {-# inline sin #-}
  {-# inline cos #-}
  {-# inline tan #-}
  {-# inline asin #-}
  {-# inline acos #-}
  {-# inline atan #-}
  {-# inline sinh #-}
  {-# inline cosh #-}
  {-# inline tanh #-}
  {-# inline asinh #-}
  {-# inline acosh #-}
  {-# inline atanh #-}
  {-# inline log1p #-}
  {-# inline expm1 #-}
  {-# inline log1pexp #-}
  {-# inline log1mexp #-}

