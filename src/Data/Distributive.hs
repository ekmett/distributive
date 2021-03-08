{-# Language CPP #-}
{-# Language ConstraintKinds #-}
{-# Language DataKinds #-}
{-# Language DefaultSignatures #-}
{-# Language DeriveAnyClass #-}
{-# Language DeriveGeneric #-}
{-# Language DeriveTraversable #-}
#if __GLASGOW_HASKELL__ >= 802
{-# Language DerivingStrategies #-}
#endif
#if __GLASGOW_HASKELL__ >= 806
{-# Language DerivingVia #-}
#endif
{-# Language FlexibleContexts #-}
{-# Language FlexibleInstances #-}
{-# Language FunctionalDependencies #-}
{-# Language GeneralizedNewtypeDeriving #-}
{-# Language LambdaCase #-}
{-# Language PatternSynonyms #-}
{-# Language PolyKinds #-}
{-# Language RankNTypes #-}
{-# Language ScopedTypeVariables #-}
{-# Language StandaloneDeriving #-}
{-# Language Trustworthy #-}
{-# Language TypeFamilies #-}
{-# Language TypeOperators #-}
{-# Language UndecidableInstances #-}
{-# Language UndecidableSuperClasses #-}
{-# Language ViewPatterns #-}
-- |
-- Module      : Data.Distributive
-- Copyright   : (C) 2011-2021 Edward Kmett,
--               (c) 2018 Aaron Vargo,
--               (c) 2021 Oleg Grenrus
-- License     : BSD-style (see the file LICENSE)
--
-- Maintainer  : Edward Kmett <ekmett@gmail.com>
-- Stability   : provisional
-- Portability : non-portable (ghc 8.0+)
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
--   tabulate f = Moore (f []) (\\x -> tabulate $ f . (x:))
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
  -- ** via Generics
  , tabulateRep
  , indexRep
  , scatterRep
  -- ** Simple Scattering
  , scatterDefault
  -- ** Canonical 'Logarithm's
  , Logarithm(..)
  , tabulateLogarithm
  , indexLogarithm
  -- ** via DerivingVia
  , Dist(..)
  -- ** for other classes
  -- *** Functor
  , fmapDist
  -- *** Applicative
  , pureDist
  , apDist
  , liftD2
  , liftD3
  , liftD4
  , liftD5
  -- *** Monad
  , bindDist
  -- *** MonadFix
  , mfixDist
  -- *** MonadZip
  , mzipWithDist
  -- *** MonadReader
  , askDist
  -- *** Comonad
  , extractDist, extractDistBy
  , extendDist, extendDistBy
  , duplicateDist, duplicateDistBy
  -- *** ComonadTrace
  , traceDist
  -- *** FunctorWithIndex
  , imapDist
  -- *** FoldableWithIndex
  , ifoldMapDist
  -- *** TraversableWithIndex
  , itraverseDist
  -- * Tabulated endomorphisms
  , DistEndo(..)
  , tabulateDistEndo
  , indexDistEndo
  ) where

import Control.Applicative
import Control.Applicative.Backwards
import Control.Arrow
import Control.Monad.Fix
import Control.Monad.Reader
import Control.Monad.Trans.Identity
import Control.Monad.Zip
import Data.Coerce
import Data.Complex
import Data.Foldable (fold)
import Data.Functor.Compose
import Data.Functor.Identity
import Data.Functor.Product
import Data.Functor.Reverse
import Data.Kind
import qualified Data.Monoid as Monoid
import qualified Data.Semigroup as Semigroup
import Data.HKD
import Data.Ord (Down(..))
import Data.Orphans ()
import Data.Proxy
import Data.Void
import GHC.Generics
import Data.Type.Bool (type (||))

#if __GLASGOW_HASKELL__ < 804
import Data.Semigroup (Semigroup(..))
#endif

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
class Functor f => Distributive f where
  -- | Defaults to @'Log' ('Rep1' f)@ when @f@ is non-recursive, otherwise to 'Logarithm'.
  type Log f
  type Log f = DefaultLog f

  -- | Defaults to 'tabulateRep' when @f@ is non-recursive, otherwise to 'tabulateLogarithm'.
  tabulate :: (Log f -> a) -> f a
  default tabulate
    :: (Generic1 f, DefaultTabulate f)
    => (Log f -> a) -> f a
  tabulate = defaultTabulate (Proxy :: Proxy (ContainsRec1 (Rep1 f)))
  {-# inline tabulate #-}

  -- | Defaults to 'indexRep when @f@ is non-recursive, otherwise to 'indexLogarithm'.
  index :: f a -> Log f -> a
  default index
     :: (Generic1 f, DefaultIndex f)
     => f a -> Log f -> a
  index = defaultIndex (Proxy :: Proxy (ContainsRec1 (Rep1 f)))
  {-# inline index #-}

  -- | Scatter the contents of an 'FFunctor'. This admittedly complicated operation
  -- is necessary to get asymptotically optimal performance for 'Distributive' functors
  -- like Mealy and Moore machines that have many layers to them.
  --
  -- If you have a 'Generic1' instance for your 'Functor', this should be able to be
  -- generated automatically. Otherwise, if you must, you can use 'scatterDefault' as
  -- a fallback in terms of 'tabulate' and 'index', which is offered in terms of the
  -- law relating 'scatter' to 'tabulate' and 'index':
  --
  -- @
  -- 'scatter' phi wg ≡ 'tabulate' $ \\x -> 'ffmap' (\\g -> 'Identity' '$' 'index' (phi g) x) wg
  -- @
  --
  -- Defaults to 'scatterRep'
  scatter :: FFunctor w => (w Identity -> r) -> (g ~> f) -> w g -> f r
  default scatter
    :: (Generic1 f, Distributive (Rep1 f), FFunctor w)
    => (w Identity -> r) -> (g ~> f) -> w g -> f r
  scatter = scatterRep
  {-# inline scatter #-}

tabulateRep
  :: forall f a.
     (Distributive (Rep1 f), Generic1 f, Coercible (Log f) (Log (Rep1 f)))
  => (Log f -> a) -> f a
tabulateRep = coerce (to1 . tabulate :: (Log (Rep1 f) -> a) -> f a)
{-# inline tabulateRep #-}

indexRep
  :: forall f a.
     (Distributive (Rep1 f), Generic1 f, Coercible (Log f) (Log (Rep1 f)))
  => f a -> Log f -> a
indexRep = coerce (index . from1 :: f a -> Log (Rep1 f) -> a)
{-# inline indexRep #-}

scatterRep
  :: (Distributive (Rep1 f), Generic1 f, FFunctor w)
  => (w Identity -> r) -> (g ~> f) -> w g -> f r
scatterRep k phi = to1 . scatter k (from1 . phi)
{-# inline scatterRep #-}

-- * Generic derivation

-- Does Generic Rep contain 'Rec1'?
type family ContainsRec1 (f :: Type -> Type) :: Bool where
  ContainsRec1 (K1 _ _)   = 'False
  ContainsRec1 (M1 _ _ f) = ContainsRec1 f
  ContainsRec1 U1         = 'False
  ContainsRec1 V1         = 'False
  ContainsRec1 (Rec1 _)   = 'True
  ContainsRec1 Par1       = 'False
  ContainsRec1 (f :*: g)  = ContainsRec1 f || ContainsRec1 g
  ContainsRec1 (f :+: g)  = ContainsRec1 f || ContainsRec1 g
  ContainsRec1 (f :.: g)  = ContainsRec1 f || ContainsRec1 g

type family DefaultLog' (containsRec1 :: Bool) f :: Type where
  DefaultLog' 'True  f = Logarithm f
  DefaultLog' 'False f = Log (Rep1 f)

type family DefaultImplC (containsRec1 :: Bool) f :: Constraint where
  DefaultImplC 'True  f = (Distributive f, Log f ~ Logarithm f)
  DefaultImplC 'False f = (Generic1 f, Distributive (Rep1 f), Coercible (Log f) (Log (Rep1 f)))

-- individual type classes, so there is GHC needs to less work
class DefaultImplC containsRec1 f => DefaultTabulate' (containsRec1 :: Bool) f where
  defaultTabulate :: Proxy containsRec1 -> (Log f -> a) -> f a

instance DefaultImplC 'True f => DefaultTabulate' 'True f where
  defaultTabulate _ = tabulateLogarithm
  {-# inline defaultTabulate #-}

instance DefaultImplC 'False f => DefaultTabulate' 'False f where
  defaultTabulate _ = tabulateRep
  {-# inline defaultTabulate #-}

class DefaultImplC containsRec1 f => DefaultIndex' (containsRec1 :: Bool) f where
  defaultIndex :: Proxy containsRec1 -> f a -> Log f -> a

instance DefaultImplC 'True f => DefaultIndex' 'True f where
  defaultIndex _ = indexLogarithm
  {-# inline defaultIndex #-}

instance DefaultImplC 'False f => DefaultIndex' 'False f where
  defaultIndex _ = indexRep
  {-# inline defaultIndex #-}

type DefaultLog f = DefaultLog' (ContainsRec1 (Rep1 f)) f
type DefaultTabulate f = DefaultTabulate' (ContainsRec1 (Rep1 f)) f
type DefaultIndex f = DefaultIndex' (ContainsRec1 (Rep1 f)) f

-- | A helper for the most common usage pattern when working with higher-kinded data.
--
-- @
-- 'distrib' w k ≡ 'scatter' k id w
-- @
distrib :: (Distributive f, FFunctor w) => w f -> (w Identity -> r) -> f r
distrib w k = scatter k id w
{-# inline distrib #-}

-- | Implements 'scatter' in terms of 'tabulate' and 'index' by the law
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
scatterDefault k phi wg = tabulate $ \x -> k $ ffmap (\g -> Identity $ index (phi g) x) wg
{-# inline scatterDefault #-}

-- | Default definition for 'tabulate' in when 'Log f' = 'Logarithm f'. Can be used
-- to manipulate 'Logarithm's regardless of the choice of 'Log' for your distributive
-- functor.
tabulateLogarithm :: Distributive f => (Logarithm f -> a) -> f a
tabulateLogarithm f =
  distrib (Tab f) $ \(Tab f') -> f' (Logarithm runIdentity)
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
distribute f = distrib (DCompose f) $ \(DCompose f') -> runIdentity <$> f'
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
collect f fa = distrib (DCompose f) $ \(DCompose f') -> coerce f' <$> fa
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
cotraverse fab fga = distrib (DCompose fga) $ \(DCompose f') -> fab (runIdentity <$> f')
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
  type Log (Rec1 f) = Logarithm f
  scatter k f = Rec1 #. scatter k (unRec1 #. f)
  index = indexLogarithm .# unRec1
  tabulate = Rec1 #. tabulateLogarithm
  {-# inline scatter #-}
  {-# inline tabulate #-}
  {-# inline index #-}

instance Distributive Par1 where
  type Log Par1 = ()
  scatter k f = coerce $ k .  ffmap ((Identity . unPar1) #. f)
  index x () = unPar1 x
  tabulate f = Par1 $ f ()
  {-# inline scatter #-}
  {-# inline tabulate #-}
  {-# inline index #-}

newtype AppCompose w g f = AppCompose { runAppCompose :: w (f :.: g) }
instance FFunctor w => FFunctor (AppCompose w g) where
  ffmap f = AppCompose #. ffmap (Comp1 #. f .# unComp1) .# runAppCompose
  {-# inline ffmap #-}

instance (Distributive f, Distributive g) => Distributive (f :.: g) where
  type Log (f :.: g) = (Log f, Log g)
  scatter k phi wg = Comp1 $ scatter (scatter k (runIdentity #.# unComp1) .# runAppCompose) id (AppCompose (ffmap phi wg))
  index (Comp1 f) (x, y) = index (index f x) y
  tabulate f = Comp1 $ tabulate $ \i -> tabulate $ \j -> f (i, j)
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

#if MIN_VERSION_base(4,12,0)

instance Distributive Down
instance Distributive Monoid.Product
instance Distributive Monoid.Sum

#else

-- accessor isn't included in the newtype until base 4.14
getDown :: Down a -> a
getDown (Down x) = x

instance Distributive Down where
  type Log Down = ()
  scatter k f = coerce $ k . ffmap ((Identity . getDown) #. f)
  index x () = getDown x
  tabulate f = Down $ f ()
  {-# inline scatter #-}
  {-# inline tabulate #-}
  {-# inline index #-}

instance Distributive Monoid.Product where
  type Log Monoid.Product = ()
  scatter k f = coerce $ k .  ffmap ((Identity . Monoid.getProduct) #. f)
  index x () = Monoid.getProduct x
  tabulate f = Monoid.Product $ f ()
  {-# inline scatter #-}
  {-# inline tabulate #-}
  {-# inline index #-}

instance Distributive Monoid.Sum where
  type Log Monoid.Sum = ()
  scatter k f = coerce $ (k .  ffmap ((Identity . Monoid.getSum) #. f))
  index x () = Monoid.getSum x
  tabulate f = Monoid.Sum $ f ()
  {-# inline scatter #-}
  {-# inline tabulate #-}
  {-# inline index #-}

#endif

#if __GLASGOW_HASKELL__ >= 806

deriving newtype instance Distributive f => Distributive (Backwards f)
deriving newtype instance Distributive f => Distributive (Reverse f)
deriving newtype instance Distributive f => Distributive (Monoid.Alt f)
deriving newtype instance Distributive f => Distributive (Monoid.Ap f)
instance Distributive Monoid.Dual

#else

instance Distributive f => Distributive (Backwards f) where
  type Log (Backwards f) = Log f
  scatter k f = coerce $ scatter k (forwards #. f)
  index = index .# forwards
  tabulate = Backwards #. tabulate
  {-# inline scatter #-}
  {-# inline tabulate #-}
  {-# inline index #-}

instance Distributive f => Distributive (Reverse f) where
  type Log (Reverse f) = Log f
  scatter k f = coerce $ scatter k (getReverse #. f)
  index = index .# getReverse
  tabulate = Reverse #. tabulate
  {-# inline scatter #-}
  {-# inline tabulate #-}
  {-# inline index #-}

instance Distributive f => Distributive (Monoid.Alt f) where
  type Log (Monoid.Alt f) = Log f
  scatter k f = coerce $ scatter k (Monoid.getAlt #. f)
  index = index .# Monoid.getAlt
  tabulate = Monoid.Alt #. tabulate
  {-# inline scatter #-}
  {-# inline tabulate #-}
  {-# inline index #-}

#if MIN_VERSION_base(4,12,0)
instance Distributive f => Distributive (Monoid.Ap f) where
  type Log (Monoid.Ap f) = Log f
  scatter k f = coerce $ scatter k (Monoid.getAp #. f)
  index = index .# Monoid.getAp
  tabulate = Monoid.Ap #. tabulate
  {-# inline scatter #-}
  {-# inline tabulate #-}
  {-# inline index #-}
#endif

instance Distributive Monoid.Dual where
  type Log Monoid.Dual = ()
  scatter k f = coerce $ k .  ffmap ((Identity . Monoid.getDual) #. f)
  index x () = Monoid.getDual x
  tabulate f = Monoid.Dual $ f ()
  {-# inline scatter #-}
  {-# inline tabulate #-}
  {-# inline index #-}

#endif

instance Distributive Semigroup.First
instance Distributive Semigroup.Last
instance Distributive Semigroup.Min
instance Distributive Semigroup.Max
instance (Distributive f, Monad f) => Distributive (WrappedMonad f)

#if MIN_VERSION_base(4,14,0)

instance Distributive f => Distributive (Kleisli f a)

#else

instance Distributive f => Distributive (Kleisli f a) where
  type Log (Kleisli f a) = (a, Log f)
  scatter k f = coerce $ scatter k ((Comp1 . runKleisli) #. f)
  tabulate = (Kleisli . unComp1) #. tabulate
  index = index .# (Comp1 . runKleisli)
  {-# inline scatter #-}
  {-# inline tabulate #-}
  {-# inline index #-}

#endif

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

#if __GLASGOW_HASKELL__ >= 802

deriving newtype instance Distributive f => Distributive (IdentityT f)

#else

instance Distributive f => Distributive (IdentityT f) where
  type Log (IdentityT f) = Log f
  type Log (IdentityT f) = Log f
  scatter k f = coerce $ scatter k (runIdentityT #. f)
  index = index .# runIdentityT
  tabulate = IdentityT #. tabulate
  {-# inline scatter #-}
  {-# inline tabulate #-}
  {-# inline index #-}

#endif

#if __GLASGOW_HASKELL__ >= 806

deriving via ((((->) e) :.: f) :: Type -> Type)
  instance Distributive f => Distributive (ReaderT e f)

#else

instance Distributive f => Distributive (ReaderT e f) where
  type Log (ReaderT e f) = (e, Log f)
  scatter k f = coerce $ scatter k ((Comp1 . runReaderT) #. f)
  tabulate = (ReaderT . unComp1) #. tabulate
  index = index .# (Comp1 . runReaderT)

#endif

-- * DerivingVia

-- | Provides defaults definitions for other classes in terms of
-- 'Distributive'. Supplied for use with @DerivingVia@ in GHC 8.6+
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

-- * Applicative

instance Distributive f => Applicative (Dist f) where
  pure = pureDist
  {-# inline pure #-}
  (<*>) = apDist
  {-# inline (<*>) #-}
  _ *> m = m
  {-# inline (*>) #-}
  (<*) = const
  {-# inline (<*) #-}
#if MIN_VERSION_base(4,10,0)
  liftA2 = liftD2
  {-# inline liftA2 #-}
#endif

-- | A default definition for 'fmap' from 'Functor' in terms of 'Distributive'
fmapDist :: Distributive f => (a -> b) -> f a -> f b
fmapDist f fa = distrib (Element fa) $ \(Element (Identity a)) -> f a
{-# inline fmapDist #-}

-- | A default definition for 'pure' from 'Applicative' in terms of 'Distributive'
pureDist :: Distributive f => a -> f a
pureDist = tabulate . const
{-# inline pureDist #-}

data D2 a b f = D2 (f a) (f b)
instance FFunctor (D2 a b) where
  ffmap f (D2 a b) = D2 (f a) (f b)
  {-# inline ffmap #-}

-- | A default definition for '(<*>)' from 'Applicative' in terms of 'Distributive'
apDist :: Distributive f => f (a -> b) -> f a -> f b
apDist fab fa = distrib (D2 fab fa) $ \(D2 ab a) -> coerce ab a
{-# inline apDist #-}

-- | A default definition 'liftA2' from 'Applicative' in terms of 'Distributive'
liftD2 :: Distributive f => (a -> b -> c) -> f a -> f b -> f c
liftD2 f fa fb = distrib (D2 fa fb) $ \(D2 a b) -> coerce f a b
{-# inline liftD2 #-}

data D3 a b c f = D3 (f a) (f b) (f c)
instance FFunctor (D3 a b c) where
  ffmap f (D3 a b c) = D3 (f a) (f b) (f c)
  {-# inline ffmap #-}

-- | An implementation of 'liftA3' in terms of 'Distributive'.
liftD3 :: Distributive f => (a -> b -> c -> d) -> f a -> f b -> f c -> f d
liftD3 f fa fb fc = distrib (D3 fa fb fc) $ \(D3 a b c) -> coerce f a b c
{-# inline liftD3 #-}

data D4 a b c d f = D4 (f a) (f b) (f c) (f d)
instance FFunctor (D4 a b c d) where
  ffmap f (D4 a b c d) = D4 (f a) (f b) (f c) (f d)
  {-# inline ffmap #-}

-- | An implementation of 'liftA4' in terms of 'Distributive'.
liftD4 :: Distributive f => (a -> b -> c -> d -> e) -> f a -> f b -> f c -> f d -> f e
liftD4 f fa fb fc fd = distrib (D4 fa fb fc fd) $ \(D4 a b c d) -> coerce f a b c d
{-# inline liftD4 #-}

data D5 a b c d e f = D5 (f a) (f b) (f c) (f d) (f e)
instance FFunctor (D5 a b c d e) where
  ffmap f (D5 a b c d e) = D5 (f a) (f b) (f c) (f d) (f e)
  {-# inline ffmap #-}

-- | An implementation of 'liftA5' in terms of 'Distributive'.
liftD5 :: Distributive f => (a -> b -> c -> d -> e -> x) -> f a -> f b -> f c -> f d -> f e -> f x
liftD5 f fa fb fc fd fe = distrib (D5 fa fb fc fd fe) $ \(D5 a b c d e) -> coerce f a b c d e
{-# inline liftD5 #-}

-- * Monad

data DBind x y f = DBind (f x) (x -> f y)
instance FFunctor (DBind x y) where
  ffmap f (DBind l r) = DBind (f l) (f . r)
  {-# inline ffmap #-}

instance Distributive f => Monad (Dist f) where
  (>>=) = bindDist
  {-# inline (>>=) #-}

-- | A default implementation of '(>>=)' in terms of 'Distributive'
bindDist :: Distributive f => f a -> (a -> f b) -> f b
bindDist m f = distrib (DBind m f) $ \(DBind (Identity a) f') -> runIdentity (f' a)
{-# inline bindDist #-}

-- * MonadFix

instance Distributive f => MonadFix (Dist f) where
  mfix = mfixDist
  {-# inline mfix #-}

-- | A default definition for 'mfix' in terms of 'Distributive'
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

-- * MonadZip

-- | A default definition for 'mzipWith' in terms of 'Distributive'
mzipWithDist :: Distributive f => (a -> b -> c) -> f a -> f b -> f c
mzipWithDist = liftD2
{-# inline mzipWithDist #-}

-- * Comonad

-- instance (Distributive f, Monoid (Log f)) => Comonad (Dist f) where
--  extract = extractDist
--  {-# inline extract #-}
--  duplicate = duplicateDist
--  {-# inline duplicate #-}
--  extend = extendDist
--  {-# inline extend #-}

-- | A default definition for 'extract' from @Comonad@ in terms of 'Distributive'
extractDist :: (Distributive f, Monoid (Log f)) => f a -> a
extractDist = flip index mempty
{-# inline extractDist #-}

-- | A default definition for 'extend' from @Comonad@ in terms of 'Distributive'
extendDist :: (Distributive f, Semigroup (Log f)) => (f a -> b) -> f a -> f b
extendDist f g = tabulate $ \i -> f $ tabulate $ \j -> index g (i <> j)
{-# inline extendDist #-}

-- | A default definition for 'duplicate' from @Comonad@ in terms of 'Distributive'
duplicateDist :: (Distributive f, Semigroup (Log f)) => f a -> f (f a)
duplicateDist f = tabulate $ \i -> tabulate $ \j -> index f (i <> j)
{-# inline duplicateDist #-}

-- | A default definition for 'extract' from @Comonad@ in terms of 'Distributive'
-- where the user chooses to supply a 'unit' logarithm other than 'mempty'
extractDistBy :: Distributive f => Log f -> f a -> a
extractDistBy = flip index
{-# inline extractDistBy #-}

-- | A default definition for 'extend' from @Comonad@ in terms of 'Distributive'
-- where the user chooses to supply a semigroup on logarithms other than '<>'
extendDistBy :: Distributive f => (Log f -> Log f -> Log f) -> (f a -> b) -> f a -> f b
extendDistBy t f g = tabulate $ \i -> f $ tabulate $ \j -> index g (t i j)

{-# inline extendDistBy #-}
-- | A default definition for 'duplicate' from @Comonad@ in terms of 'Distributive'
-- where the user chooses to supply an semigroup on logarithms other than '<>'
duplicateDistBy :: Distributive f => (Log f -> Log f -> Log f) -> f a -> f (f a)
duplicateDistBy t f = tabulate $ \i -> tabulate $ \j -> index f (t i j)
{-# inline duplicateDistBy #-}

-- * MonadReader

-- deriving via (f :.: ((->) e)) instance Distributive f => Distributive (TracedT e f)

-- | A default definition for 'ask' from 'MonadReader' in terms of 'Distributive'
askDist :: Distributive f => f (Log f)
askDist = tabulate id
{-# inline askDist #-}

-- | A default definition for 'local' from 'MonadReader' in terms of 'Distributive'
localDist :: Distributive f => (Log f -> Log f) -> f a -> f a
localDist f m = tabulate (index m . f)
{-# inline localDist #-}

-- * ComonadTrace

-- | A default definition for 'trace' from @ComonadTrace@ in terms of 'Distributive'
traceDist :: Distributive f => Log f -> f a -> a
traceDist = flip index
{-# inline traceDist #-}

-- * FunctorWithIndex

-- | A default definition for 'imap' from @FunctorWithIndex@ in terms of 'Distributive'
imapDist
  :: Distributive f
  => (Log f -> a -> b) -> f a -> f b
imapDist f xs = tabulate (f <*> index xs)

-- * FoldableWithIndex

-- | A default definition for 'ifoldMap' from @FoldableWithIndex@ in terms of 'Distributive'
ifoldMapDist
  :: forall f m a.
     (Distributive f, Foldable f, Monoid m)
  => (Log f -> a -> m) -> f a -> m
ifoldMapDist ix xs = fold (tabulate (\i -> ix i $ index xs i) :: f m)

-- * TraversableWithIndex

-- | A default definition for 'itraverse' from @TraversableWithIndex@ in terms of 'Distributive'
itraverseDist
  :: forall f m a b.
     (Distributive f, Traversable f, Applicative m)
  => (Log f -> a -> m b) -> f a -> m (f b)
itraverseDist ix xs = sequenceA $ tabulate (ix <*> index xs)

-- | Tabulated endomorphisms.
--
-- Many representable functors can be used to memoize functions.
newtype DistEndo f = DistEndo { runDistEndo :: f (Log f) }

instance Distributive f => Semigroup (DistEndo f) where
  DistEndo f <> DistEndo g = DistEndo $ tabulate $ \x -> index f (index g x)
  {-# inline (<>) #-}

instance Distributive f => Monoid (DistEndo f) where
#if __GLASGOW_HASKELL__ < 804
  DistEndo f `mappend` DistEndo g = DistEndo $ tabulate $ \x -> index f (index g x)
  {-# inline mappend #-}
#endif
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

(#.#) :: Coercible a c => (b -> c) -> (a -> b) -> a -> c
_ #.# _ = coerce
{-# inline (#.#) #-}

infixr 9 #., .#, #.#
