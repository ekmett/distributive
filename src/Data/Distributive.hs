{-# Language CPP #-}
{-# Language BlockArguments #-}
{-# Language DefaultSignatures #-}
{-# Language DeriveAnyClass #-}
{-# Language DeriveGeneric #-}
{-# Language DeriveTraversable #-}
{-# Language DerivingStrategies #-}
{-# Language DerivingVia #-}
{-# Language FlexibleContexts #-}
{-# Language FlexibleInstances #-}
{-# Language GeneralizedNewtypeDeriving #-}
{-# Language MultiParamTypeClasses #-}
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
-- If you want a special form for the 'Log' of your functor you can
-- implement tabulate and index directly, `Dist` can still be used.
--
-- @
--
-- data Moore a b = Moore b (a -> Moore a b)
--   deriving stock Functor
--   deriving (Comonad, Applicative, Monad, MonadFix, MonadZip) via Dist (Moore a)
--   
-- instance Distributive (Moore a) where
--   type Log (Moore a) = [a]
--   tabulate f = Moore (f []) (\x -> tabulate $ f . (x:))
--   index (Moore a _) [] = a
--   index (Moore _ as) (x:xs) = index (as x) xs
-- @
module Data.Distributive
  ( Distributive(..)


  , distrib
  , distribute
  , collect
  , cotraverse
  -- * Default definitions 
  , Dist(..)
  -- * Applicative
  , apDist
  , liftD2
  , liftD3
  -- * Monad
  , bindDist
  -- * MonadFix
  , mfixDist
  -- * MonadZip
  , mzipWithRep
  -- * MonadReader
  , askDist
  -- * Comonad
  , extractDist, extractDistBy
  , extendDist, extendDistBy
  , duplicateDist, duplicateDistBy
  , traceDist
  -- * Tabulated endomorphisms
  , DistEndo(..)
  , tabulateDistEndo
  , indexDistEndo
  -- * "Flat" 'scatter' in terms of 'tabulate'/'index'
  , scatterDefault
  -- * Default choice of representation
  , Logarithm(..)
  , tabulateLogarithm
  , indexLogarithm
  ) where

import Control.Applicative
import Control.Arrow
import Control.Monad.Fix
import Control.Monad.Reader
import Control.Monad.Trans.Identity
import Control.Monad.Zip
import Data.Coerce
import Data.Complex
import Data.Functor.Compose
import Data.Functor.Identity
import Data.Functor.Product
import qualified Data.Monoid as Monoid
import qualified Data.Semigroup as Semigroup
import Data.HKD
import Data.Kind
import Data.Ord (Down)
import Data.Proxy
import Data.Void
import GHC.Generics

-- import Control.Comonad
-- import Control.Comonad.Traced (TracedT(..))

#ifdef MIN_VERSION_tagged
import Data.Tagged
#endif

-- | The dual of a 'Traversable' functor.
--
-- Due to the lack of non-trivial comonoids in Haskell, we can restrict
-- ourselves to requiring a 'Functor' rather than some Coapplicative class.
-- Categorically every 'Distributive' functor is actually a right adjoint,
-- and so it must be 'Representable' endofunctor and preserve all limits.
-- This is a fancy way of saying @f@ is isomorphic to @(->) x@ for some x.
-- We use the name @Log f@ for @x@.
--
-- 
-- @
-- 'tabulate' '.' 'index' ≡ 'id'
-- 'index' '.' 'tabulate' ≡ 'id'
-- @
--
-- To be distributable a container will need to have a way to consistently
-- zip a potentially infinite number of copies of itself. This effectively
-- means that the holes in all values of that type, must have the same
-- cardinality, fixed sized vectors, infinite streams, functions, etc.
-- and no extra information to try to merge together.
class Functor f => Distributive (f :: Type -> Type) where
  -- If the user doesn't specify a meaning for 'Log', we default to 'Logarithm'
  -- from the @hkd@ package.
  type Log f :: Type
  type Log f = Logarithm f

  tabulate :: (Log f -> a) -> f a
  default tabulate :: (Log f ~ Logarithm f) => (Log f -> a) -> f a
  tabulate = tabulateLogarithm
  {-# inline tabulate #-}

  index :: f a -> Log f -> a
  default index :: (Log f ~ Logarithm f) => f a -> Log f -> a
  index = indexLogarithm
  {-# inline index #-}

  -- | Scatter the contents of an 'FFunctor'. This admittedly complicated operation
  -- is necessary to get asymptotically optimal performance for 'Distributive' functors
  -- like Mealy and Moore machines that have many layers to them.
  --
  -- 'scatter' is the central defining method in the class, rather than 'distrib'
  -- because on one hand, we would not be able to use @GeneralizedNewtypeDeriving@
  -- if we made the other choice, but also to allow us to fuse more operations
  -- together in the 'Generic1'-driven default implementation of the class.
  --
  -- If you have a 'Generic1' instance for your 'Functor', this should be able to be
  -- generated automatically
  --
  -- @
  -- 'scatter' phi wg = 'tabulate' \x -> 'ffmap' (\g -> 'Identity' $ 'index' (phi g) x) wg
  -- @
  scatter :: FFunctor w => (w Identity -> r) -> (g ~> f) -> w g -> f r
  default scatter
    :: (Generic1 f, Distributive (Rep1 f), FFunctor w)
    => (w Identity -> r) -> (g ~> f) -> w g -> f r
  scatter k phi = to1 . scatter k (from1 . phi)
  {-# inline scatter #-}

distrib :: (Distributive f, FFunctor w) => w f -> (w Identity -> r) -> f r
distrib w k = scatter k id w
{-# inline distrib #-}

-- | implement 'scatter' in terms of 'tabulate' and 'index' by the law
-- that relates 'scatter' to its canonical implementation.
--
-- This might be useful if you define custom 'tabulate' and 'index' functions
-- but do not need to carefully peel apart your structure layer by layer and
-- for some reason you are unable to define 'Generic1' and so canot simply use
-- 'DeriveAnyClass'.
scatterDefault
  :: (Distributive f, FFunctor w)
  => (w Identity -> r)
  -> (g ~> f)
  -> w g -> f r
scatterDefault k phi wg = tabulate \x -> k $ ffmap (\g -> Identity $ index (phi g) x) wg
{-# inline scatterDefault #-}

-- | Default definition for 'tabulate' in when 'Log f' = 'Logarithm f'. Can be used
-- to manipulate 'Logarithm's regardless of the choice of 'Log' for your distributive
-- functor.
tabulateLogarithm :: Distributive f => (Logarithm f -> a) -> f a
tabulateLogarithm f =
  distrib (Tab f) \(Tab f') -> f' (Logarithm runIdentity)
{-# inline tabulateLogarithm #-}

newtype DCompose a f g = DCompose { runDCompose :: f (g a) }
instance Functor f => FFunctor (DCompose a f) where
  ffmap f = DCompose #. (fmap f .# runDCompose)
  {-# inline ffmap #-}

-- | The dual of 'Data.Traversable.sequenceA'
--
-- >>> distribute [(+1),(+2)] 1
-- [2,3]
--
-- @
-- 'distribute' = 'collect' 'id'
-- 'distribute' . 'distribute' = 'id'
-- @
distribute
  :: (Functor f, Distributive g)
  => f (g a) -> g (f a)
distribute f = distrib (DCompose f) \(DCompose f') -> runIdentity <$> f'
{-# inline distribute #-}

-- |
-- @
-- 'collect' f = 'distribute' . 'fmap' f
-- 'fmap' f = 'runIdentity' . 'collect' ('Identity' . f)
-- 'fmap' 'distribute' . 'collect' f = 'getCompose' . 'collect' ('Compose' . f)
-- @
collect
  :: (Functor f, Distributive g)
  => (a -> g b)
  -> f a -> g (f b)
collect f fa = distrib (DCompose f) \(DCompose f') -> coerce f' <$> fa
{-# inline collect #-}

-- | The dual of 'Data.Traversable.traverse'
--
-- @
-- 'cotraverse' f = 'fmap' f . 'distribute'
-- @
cotraverse
  :: (Functor f, Distributive g)
  => (f a -> b)
  -> f (g a) -> g b
cotraverse fab fga = distrib (DCompose fga) \(DCompose f') -> fab (runIdentity <$> f')
{-# inline cotraverse #-}

instance (Distributive f, Distributive g) => Distributive (f :*: g) where
  type Log (f :*: g) = Either (Log f) (Log g)
  scatter k f (ffmap f -> w)
      = scatter k (\(l :*: _) -> l) w
    :*: scatter k (\(_ :*: r) -> r) w
  tabulate f = tabulate (f . Left) :*: tabulate (f . Right)
  index (f :*: _) (Left x) = index f x
  index (_ :*: g) (Right y) = index g y
  {-# inline scatter #-}
  {-# inline tabulate #-}
  {-# inline index #-}

instance Distributive f => Distributive (M1 i c f) where
  type Log (M1 i c f) = Log f
  scatter k f = M1 #. scatter k (unM1 #. f)
  index = index .# unM1
  tabulate = M1 #. tabulate
  {-# inline scatter #-}
  {-# inline tabulate #-}
  {-# inline index #-}

instance Distributive U1 where
  type Log U1 = Void
  scatter _ _ _ = U1
  tabulate _ = U1
  index _ = absurd
  {-# inline scatter #-}
  {-# inline tabulate #-}
  {-# inline index #-}

instance Distributive f => Distributive (Rec1 f) where
  type Log (Rec1 f) = Log f
  scatter k f = Rec1 #. scatter k (unRec1 #. f)
  index = index .# unRec1
  tabulate = Rec1 #. tabulate
  {-# inline scatter #-}
  {-# inline tabulate #-}
  {-# inline index #-}

instance Distributive Par1 where
  type Log Par1 = ()
  scatter k f = Par1 #. (k .  ffmap ((Identity . unPar1) #. f))
  index x () = unPar1 x
  tabulate f = Par1 $ f ()
  {-# inline scatter #-}
  {-# inline tabulate #-}
  {-# inline index #-}

instance (Distributive f, Distributive g) => Distributive (f :.: g) where
  type Log (f :.: g) = (Log f, Log g)
  scatter = scatterDefault
  index (Comp1 f) (x, y) = index (index f x) y
  tabulate f = Comp1 $ tabulate \i -> tabulate \j -> f (i, j)
  {-# inline scatter #-}
  {-# inline tabulate #-}
  {-# inline index #-}

instance (Distributive f, Distributive g) => Distributive (Compose f g)
instance (Distributive f, Distributive g) => Distributive (Product f g)

instance Distributive Proxy

instance Distributive Identity
instance Distributive ((->) x) where
  type Log ((->) x) = x
  scatter k phi wg x = k $ ffmap (\g -> Identity $ phi g x) wg
  tabulate = id
  index = id
  {-# inline scatter #-}
  {-# inline tabulate #-}
  {-# inline index #-}

instance Distributive Down
instance Distributive Monoid.Product
instance Distributive Monoid.Sum
instance Distributive f => Distributive (Monoid.Alt f)
instance Distributive f => Distributive (Monoid.Ap f)
instance Distributive Monoid.Dual
instance Distributive Semigroup.First
instance Distributive Semigroup.Last
instance Distributive Semigroup.Min
instance Distributive Semigroup.Max
instance (Distributive f, Monad f) => Distributive (WrappedMonad f)
instance Distributive f => Distributive (Kleisli f a)

-- instance Distributive f => Distributive (Cokleisli f a)

#ifdef MIN_VERSION_tagged
instance Distributive (Tagged r)
#endif

instance Distributive Complex where
  type Log Complex = Bool
  tabulate f = f False :+ f True
  {-# inline tabulate #-}
  index (r :+ i) = \case
    False -> r
    True -> i
  {-# inline index #-}

deriving newtype
  instance Distributive f => Distributive (IdentityT f)

deriving via (((->) e) :.: f)
  instance Distributive f => Distributive (ReaderT e f)

-- | Provides defaults definitions for other classes in terms of
-- 'Distributive'. Supplied for use with @DerivingVia@
newtype Dist f a = Dist { runDist :: f a }

instance Distributive f => Functor (Dist f) where
  fmap = fmapDist
  {-# inline fmap #-}
  a <$ _ = pure a
  {-# inline (<$) #-}

instance Distributive f => Distributive (Dist f) where
  type Log (Dist f) = Log f
  scatter k f = Dist #. scatter k (runDist #. f) 
  tabulate = Dist #. tabulate
  index = index .# runDist
  {-# inline scatter #-}
  {-# inline tabulate #-}
  {-# inline index #-}

data DAp x y f = DAp (f x) (f y)
instance FFunctor (DAp x y) where
  ffmap f (DAp l r) = DAp (f l) (f r)
  {-# inline ffmap #-}

instance Distributive f => Applicative (Dist f) where
  pure = pureDist
  liftA2 = liftD2
  (<*>) = apDist
  _ *> m = m
  (<*) = const
  {-# inline pure #-}
  {-# inline liftA2 #-}
  {-# inline (<*>) #-}
  {-# inline (*>) #-}
  {-# inline (<*) #-}

fmapDist :: Distributive f => (a -> b) -> f a -> f b
fmapDist f fa = distrib (Element fa) \(Element (Identity a)) -> f a
{-# inline fmapDist #-}

pureDist :: Distributive f => a -> f a
pureDist = tabulate . const
{-# inline pureDist #-}

apDist :: Distributive f => f (a -> b) -> f a -> f b
apDist fab fa = distrib (DAp fab fa) \(DAp ab a) -> coerce ab a
{-# inline apDist #-}

liftD2 :: Distributive f => (a -> b -> c) -> f a -> f b -> f c
liftD2 f fa fb = distrib (DAp fa fb) \(DAp a b) -> coerce f a b
{-# inline liftD2 #-}

data DAp3 x y z f = DAp3 (f x) (f y) (f z)
instance FFunctor (DAp3 x y z) where
  ffmap f (DAp3 x y z) = DAp3 (f x) (f y) (f z)
  {-# inline ffmap #-}

liftD3 :: Distributive f => (a -> b -> c -> d) -> f a -> f b -> f c -> f d
liftD3 f fa fb fc = distrib (DAp3 fa fb fc) \(DAp3 a b c) -> coerce f a b c
{-# inline liftD3 #-}

data DBind x y f = DBind (f x) (x -> f y)
instance FFunctor (DBind x y) where
  ffmap f (DBind l r) = DBind (f l) (f . r)
  {-# inline ffmap #-}

instance Distributive f => Monad (Dist f) where
  (>>=) = bindDist
  {-# inline (>>=) #-}

bindDist :: Distributive f => f a -> (a -> f b) -> f b
bindDist m f = distrib (DBind m f) \(DBind (Identity a) f') -> runIdentity (f' a)
{-# inline bindDist #-}

instance Distributive f => MonadFix (Dist f) where
  mfix = mfixDist
  {-# inline mfix #-}

mfixDist :: Distributive f => (a -> f a) -> f a
mfixDist ama = distrib (DCompose ama) (fix . coerce)
{-# inline mfixDist #-}

instance Distributive f => MonadZip (Dist f) where
  mzipWith = liftD2
  {-# inline mzipWith #-}
  munzip = fmap fst &&& fmap snd
  {-# inline munzip #-}

instance (Distributive f, e ~ Log f) => MonadReader e (Dist f) where
  ask = askDist
  {-# inline ask #-}
  local = localDist
  {-# inline local #-}
  reader = tabulate
  {-# inline reader #-}

mzipWithRep :: Distributive f => (a -> b -> c) -> f a -> f b -> f c
mzipWithRep = liftD2
{-# inline mzipWithRep #-}
  
-- instance (Distributive f, Monoid (Log f)) => Comonad (Dist f) where
--  extract = extractRep
--  {-# inline extract #-}
--  duplicate = duplicateDist
--  {-# inline duplicate #-}
--  extend = extendDist
--  {-# inline extend #-}

-- * Comonads

extractDist :: (Distributive f, Monoid (Log f)) => f a -> a
extractDist = flip index mempty
{-# inline extractDist #-}

extendDist :: (Distributive f, Semigroup (Log f)) => (f a -> b) -> f a -> f b
extendDist f g = tabulate \i -> f $ tabulate \j -> index g (i <> j)
{-# inline extendDist #-}

duplicateDist :: (Distributive f, Semigroup (Log f)) => f a -> f (f a)
duplicateDist f = tabulate \i -> tabulate \j -> index f (i <> j)
{-# inline duplicateDist #-}

extractDistBy :: Distributive f => Log f -> f a -> a
extractDistBy = flip index
{-# inline extractDistBy #-}

extendDistBy :: Distributive f => (Log f -> Log f -> Log f) -> (f a -> b) -> f a -> f b
extendDistBy t f g = tabulate \i -> f $ tabulate \j -> index g (t i j)
{-# inline extendDistBy #-}

duplicateDistBy :: Distributive f => (Log f -> Log f -> Log f) -> f a -> f (f a)
duplicateDistBy t f = tabulate \i -> tabulate \j -> index f (t i j)
{-# inline duplicateDistBy #-}

-- deriving via (f :.: ((->) e)) instance Distributive f => Distributive (TracedT e f)

askDist :: Distributive f => f (Log f)
askDist = tabulate id
{-# inline askDist #-}

localDist :: Distributive f => (Log f -> Log f) -> f a -> f a
localDist f m = tabulate (index m . f)
{-# inline localDist #-}

-- * Default @trace@ for @ComonadTrace@'s trace.
traceDist :: Distributive f => Log f -> f a -> a
traceDist = flip index
{-# inline traceDist #-}

newtype DistEndo f = DistEndo { runDistEndo :: f (Log f) }

-- * Tabulated Endomorphisms

instance Distributive f => Semigroup (DistEndo f) where
  DistEndo f <> DistEndo g = DistEndo $ tabulate \x -> index f (index g x)
  {-# inline (<>) #-}

instance Distributive f => Monoid (DistEndo f) where
  mempty = DistEndo askDist
  {-# inline mempty #-}

indexDistEndo :: Distributive f => DistEndo f -> Log f -> Log f 
indexDistEndo = index .# runDistEndo
{-# inline indexDistEndo #-}

tabulateDistEndo :: Distributive f => (Log f -> Log f) -> DistEndo f
tabulateDistEndo = DistEndo #. tabulate
{-# inline tabulateDistEndo #-}

-- * Utilities

(#.) :: Coercible b c => (b -> c) -> (a -> b) -> a -> c
(#.) _ = coerce
{-# inline (#.) #-}

(.#) :: Coercible a b => (b -> c) -> (a -> b) -> a -> c
(.#) f _ = coerce f
{-# inline (.#) #-}

infix 9 #., .#

