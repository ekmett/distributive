{-# Language CPP #-}
{-# Language BlockArguments #-}
{-# Language DefaultSignatures #-}
{-# Language DeriveAnyClass #-}
{-# Language DeriveGeneric #-}
{-# Language DeriveTraversable #-}
{-# Language DerivingStrategies #-}
{-# Language DerivingVia #-}
{-# Language FlexibleContexts #-}
{-# Language GeneralizedNewtypeDeriving #-}
{-# Language LambdaCase #-}
{-# Language PatternSynonyms #-}
{-# Language RankNTypes #-}
{-# Language StandaloneDeriving #-}
{-# Language TypeApplications #-}
{-# Language TypeFamilies #-}
{-# Language TypeOperators #-}
{-# Language UndecidableInstances #-}
{-# Language ViewPatterns #-}
-- |
-- Module      : Data.Distributive
-- Copyright   : (C) 2011-2021 Edward Kmett, (c) 2018 Aaron Vargo
-- License     : BSD-style (see the file LICENSE)
--
-- Maintainer  : Edward Kmett <ekmett@gmail.com>
-- Stability   : provisional
-- Portability : non-portable
--
-- Examples:
--
-- For most data types you can use @GHC.Generics@ and @DeriveAnyClass@
-- along with the `Dist` newtype to fill in a ton of instances.
--
-- @
-- data V3 a = V3 a a a
--   deriving stock (Functor, Generic1)
--   deriving anyclass Distributive
--   deriving (Applicative, Monad, MonadFix, MonadZip) via Dist V3
-- @
--
-- @
-- If you want a special form for the 'Log' of your functor you can
-- implement tabulate and index directly, `Dist` can still be used.
-- @
--
-- data Moore a b = Moore b (a -> Moore a b)
--   deriving stock Functor
--   deriving (Comonad, Applicative, Monad, MonadFix, MonadZip) via Dist (Moore a)
--   
-- instance Distributive (Moore a) where
--   type Log (Moore a) = [a]
--   scatter = scatterDefault
--   tabulate f = Moore (f []) \x -> tabulate $ f . (x:)
--   index (Moore a _) [] = a
--   index (Moore _ as) (x:xs) = index (as x) xs
--
-- data Mealy a b = Mealy (a -> (b, Mealy a b)) 
--   deriving stock Functor
--   deriving (Applicative, Monad, MonadFix, MonadZip) via Dist (Mealy a)
--   
-- instance Distributive (Mealy a) where
--   type Log (Mealy a) = NonEmpty a
--   scatter = scatterDefault
--   tabulate f = Mealy \x -> (f (pure x), tabulate $ f . NE.cons x)
--   index (Mealy f) (x :| xs) = case xs of
--       [] -> y
--       x':xs' -> index ys (x':|xs')
--     where (y, ys) = f x 
-- @
module Data.Distributive
  ( Distributive(..)
  , Logarithm(..)
  , tabulateLogarithm
  , indexLogarithm
  , scatterDefault
  , distrib
  , distribute
  , collect
  , cotraverse
  , tabulation
  , extractDefault, extractWithDefault
  , extendDefault, extendWithDefault
  , duplicateDefault, duplicateWithDefault
  , DistEndo(..)
  , tabulateDistEndo
  , indexDistEndo
  ) where

import Control.Applicative
import Control.Arrow
import Control.Monad.Fix
import Control.Monad.Zip
import Data.Coerce
import Data.Complex
import Data.Functor
import Data.Functor.Compose
import Data.Functor.Identity
import Data.Functor.Product
import Data.HKD
import Data.Kind
-- import Data.List.NonEmpty as NE
import Data.Proxy
import Data.Void
import GHC.Generics

#ifdef MIN_VERSION_comonad
import Control.Comonad
import Control.Comonad.Traced (TracedT(..))
#endif

#ifdef MIN_VERSION_transformers
import Control.Monad.Trans.Identity
import Control.Monad.Trans.Reader
#endif

#ifdef MIN_VERSION_tagged
import Data.Tagged
#endif

class Functor f => Distributive (f :: Type -> Type) where
  type Log f :: Type
  type Log f = Logarithm f

  scatter :: FFunctor w => (g ~> f) -> w g -> f (w Identity)
  default scatter
    :: (Generic1 f, Distributive (Rep1 f), FFunctor w)
    => (g ~> f) -> w g -> f (w Identity)
  scatter phi = to1 . scatter (from1 . phi)

  tabulate :: (Log f -> a) -> f a
  default tabulate :: (Log f ~ Logarithm f) => (Log f -> a) -> f a
  tabulate = tabulateLogarithm

  index :: f a -> Log f -> a
  default index :: (Log f ~ Logarithm f) => f a -> Log f -> a
  index = indexLogarithm

distrib :: (Distributive f, FFunctor w) => w f -> f (w Identity)
distrib = scatter id

--- | implement in terms of tabulate and index
scatterDefault :: (Distributive f, FFunctor w) => (g ~> f) -> w g -> f (w Identity)
scatterDefault phi wg = tabulate \x -> ffmap (\g -> Identity $ index (phi g) x) wg

tabulateLogarithm :: Distributive f => (Logarithm f -> a) -> f a
tabulateLogarithm f =
  distrib (Tab f) <&> \(Tab f') -> f' (Logarithm runIdentity)

newtype DX a f g = DX { runDX :: f (g a) }
instance Functor f => FFunctor (DX a f) where
  ffmap f = DX #. (fmap f .# runDX)

distribute :: (Functor f, Distributive g) => f (g a) -> g (f a)
distribute f = distrib (DX f) <&> \(DX f') -> runIdentity <$> f'

collect :: (Functor f, Distributive g) => (a -> g b) -> f a -> g (f b)
collect f fa = distrib (DX f) <&> \(DX f') -> coerce f' <$> fa

cotraverse :: (Functor f, Distributive g) => (f a -> b) -> f (g a) -> g b
cotraverse fab fga = distrib (DX fga) <&> \(DX f') -> fab (runIdentity <$> f')

instance (Distributive f, Distributive g) => Distributive (f :*: g) where
  type Log (f :*: g) = Either (Log f) (Log g)
  scatter f (ffmap f -> w)
      = scatter (\(l :*: _) -> l) w
    :*: scatter (\(_ :*: r) -> r) w
  tabulate f = tabulate (f . Left) :*: tabulate (f . Right)
  index (f :*: _) (Left x) = index f x
  index (_ :*: g) (Right y) = index g y

instance Distributive f => Distributive (M1 i c f) where
  type Log (M1 i c f) = Log f
  scatter f = M1 #. scatter (unM1 #. f)
  index = index .# unM1
  tabulate = M1 #. tabulate

instance Distributive U1 where
  type Log U1 = Void
  scatter _ _ = U1
  tabulate _ = U1
  index _ = absurd

instance Distributive f => Distributive (Rec1 f) where
  type Log (Rec1 f) = Log f
  scatter f = Rec1 #. scatter (unRec1 #. f)
  index = index .# unRec1
  tabulate = Rec1 #. tabulate

instance Distributive Par1 where
  type Log Par1 = ()
  scatter f = Par1 #. ffmap ((Identity . unPar1) #. f)
  index x () = unPar1 x
  tabulate f = Par1 $ f ()

instance (Distributive f, Distributive g) => Distributive (f :.: g) where
  type Log (f :.: g) = (Log f, Log g)
  scatter = scatterDefault
  index (Comp1 f) (x, y) = index (index f x) y
  tabulate f = Comp1 $ tabulate \i -> tabulate \j -> f (i, j)

instance (Distributive f, Distributive g) => Distributive (Compose f g)
instance (Distributive f, Distributive g) => Distributive (Product f g)

instance Distributive Proxy

instance Distributive Identity
instance Distributive ((->) x) where
  type Log ((->) x) = x
  scatter phi wg x = ffmap (\g -> Identity $ phi g x) wg
  tabulate = id
  index = id

#ifdef MIN_VERSION_tagged
instance Distributive (Tagged r)
#endif

#ifdef MIN_VERSION_transformers
deriving newtype
  instance Distributive f => Distributive (IdentityT f)

deriving via (((->) e) :.: f)
  instance Distributive f => Distributive (ReaderT e f)
#endif

-- * Defaults, for use with @DerivingVia@

newtype Dist f a = Dist { runDist :: f a }
  deriving stock Functor

instance Distributive f => Distributive (Dist f) where
  type Log (Dist f) = Log f
  scatter f = Dist #. scatter (runDist #. f) 
  tabulate = Dist #. tabulate
  index = index .# runDist

data DAp x y f = DAp (f x) (f y)
instance FFunctor (DAp x y) where
  ffmap f (DAp l r) = DAp (f l) (f r)

instance Distributive f => Applicative (Dist f) where
  pure = tabulate . const
  liftA2 f fa fb = distrib (DAp fa fb) <&> \(DAp a b) -> coerce f a b
  fab <*> fa = distrib (DAp fab fa) <&> \(DAp ab a) -> coerce ab a
  _ *> m = m
  m <* _ = m

data DBind x y f = DBind (f x) (x -> f y)
instance FFunctor (DBind x y) where
  ffmap f (DBind l r) = DBind (f l) (f . r)

instance Distributive f => Monad (Dist f) where
  m >>= f = distrib (DBind m f) <&> \(DBind (Identity a) f') -> runIdentity (f' a)

instance Distributive f => MonadFix (Dist f) where
  mfix ama = distrib (DX ama) <&> fix . coerce

instance Distributive f => MonadZip (Dist f) where
  mzipWith = liftA2
  munzip = fmap fst &&& fmap snd
  
#ifdef MIN_VERSION_comonad
instance (Distributive f, Monoid (Log f)) => Comonad (Dist f) where
  extract f = index f mempty
  duplicate f = tabulate \i -> tabulate \j -> index f (i <> j)
  extend f g = tabulate \i -> f $ tabulate \j -> index g (i <> j)
#endif

-- * Comonads
--
extractDefault :: (Distributive f, Monoid (Log f)) => f a -> a
extractDefault = flip index mempty

extendDefault :: (Distributive f, Semigroup (Log f)) => (f a -> b) -> f a -> f b
extendDefault f g = tabulate \i -> f $ tabulate \j -> index g (i <> j)

duplicateDefault :: (Distributive f, Semigroup (Log f)) => f a -> f (f a)
duplicateDefault f = tabulate \i -> tabulate \j -> index f (i <> j)

extractWithDefault :: Distributive f => Log f -> f a -> a
extractWithDefault = flip index

extendWithDefault :: Distributive f => (Log f -> Log f -> Log f) -> (f a -> b) -> f a -> f b
extendWithDefault t f g = tabulate \i -> f $ tabulate \j -> index g (t i j)

duplicateWithDefault :: Distributive f => (Log f -> Log f -> Log f) -> f a -> f (f a)
duplicateWithDefault t f = tabulate \i -> tabulate \j -> index f (t i j)

#ifdef MIN_VERSION_comonad
deriving via (f :.: ((->) e))
  instance Distributive f => Distributive (TracedT e f)
#endif

-- * Tabulated Endomorphisms

tabulation :: Distributive f => f (Log f)
tabulation = tabulate id

newtype DistEndo f = DistEndo { runDistEndo :: f (Log f) }

instance Distributive f => Semigroup (DistEndo f) where
  DistEndo f <> DistEndo g = DistEndo $ tabulate \x -> index f (index g x)

instance Distributive f => Monoid (DistEndo f) where
  mempty = DistEndo tabulation

indexDistEndo :: Distributive f => DistEndo f -> Log f -> Log f 
indexDistEndo = index .# runDistEndo

tabulateDistEndo :: Distributive f => (Log f -> Log f) -> DistEndo f
tabulateDistEndo = DistEndo #. tabulate

instance Distributive Complex where
  type Log Complex = Bool
  scatter = scatterDefault
  tabulate f = f False :+ f True
  index (r :+ i) = \case
    False -> r
    True -> i

-- * Utilities

(#.) :: Coercible b c => (b -> c) -> (a -> b) -> a -> c
(#.) _ = coerce
{-# inline (#.) #-}

(.#) :: Coercible a b => (b -> c) -> (a -> b) -> a -> c
(.#) f _ = coerce f
{-# inline (.#) #-}

infix 9 #., .#

