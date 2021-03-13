{-# Language CPP #-}
{-# Language ConstraintKinds #-}
{-# Language DataKinds #-}
{-# Language DefaultSignatures #-}
{-# Language DeriveAnyClass #-}
{-# Language DeriveGeneric #-}
{-# Language DeriveTraversable #-}
{-# Language DerivingStrategies #-}
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
{-# Language TupleSections #-}
{-# Language TypeFamilies #-}
{-# Language TypeOperators #-}
{-# Language UndecidableInstances #-}
{-# Language UndecidableSuperClasses #-}
{-# Language ViewPatterns #-}
{-# OPTIONS_GHC -Wno-orphans #-}
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
--   deriving stock (Functor, Foldable, Traversable, Generic1)
--   deriving anyclass Distributive
--   deriving ( Applicative, Monad, MonadFix, MonadZip
--              MonadReader (Logarithm V3)
--            , FunctorWithIndex (Logarithm V3)
--            , FoldableWithIndex (Logarithm V3)
--            , TraversableWithIndex (Logarithm V3)
--            ) via Dist V3
--   deriving (Num, Fractional, Floating) via Dist V3 a
-- @
--
-- If you want a special form for the 'Log' of your functor you can
-- implement tabulate and index directly, `Dist` can still be used.
module Data.Distributive
  ( Distributive(..)
  , distrib
  , distribute
  , collect
  , cotraverse
  , pattern Tabulate
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
  , _logarithm
  , logFromLogarithm
  , logToLogarithm
  , _log
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
  -- *** As right adjoints
  , leftAdjunctDist
  , rightAdjunctDist
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
import Data.Distributive.Util
import Data.Foldable (fold)
import Data.Function (on)
import Data.Functor
import Data.Functor.Classes
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
import Data.Type.Bool (type (||))
import GHC.Generics
import GHC.TypeLits (Nat, type (-))
import Numeric

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
-- We use the name @'Log' f@ for @x@.
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
  tabulate = defaultTabulate (Proxy :: Proxy (ContainsSelfRec1 (Rep1 f) 3))
  {-# inline tabulate #-}

  -- | Defaults to 'indexRep when @f@ is non-recursive, otherwise to 'indexLogarithm'.
  index :: f a -> Log f -> a
  default index
     :: (Generic1 f, DefaultIndex f)
     => f a -> Log f -> a
  index = defaultIndex (Proxy :: Proxy (ContainsSelfRec1 (Rep1 f) 3))
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

pattern Tabulate :: Distributive f => (Log f -> a) -> f a
pattern Tabulate i <- (index -> i) where
  Tabulate i = tabulate i

-- * Generic derivation

-- Does Generic Rep contain 'Rec1'?
--
-- This is a Hack. If we loop i (= 3) times we declared we are recursive.
type family ContainsSelfRec1 (f :: Type -> Type) (i :: Nat) :: Bool where
  ContainsSelfRec1 _          0 = 'True
  ContainsSelfRec1 (K1 _ _)   i = 'False
  ContainsSelfRec1 (M1 _ _ f) i = ContainsSelfRec1 f i
  ContainsSelfRec1 U1         i = 'False
  ContainsSelfRec1 V1         i = 'False
  ContainsSelfRec1 Par1       _ = 'False
  ContainsSelfRec1 (f :*: g)  i = ContainsSelfRec1 f i || ContainsSelfRec1 g i
  ContainsSelfRec1 (f :+: g)  i = ContainsSelfRec1 f i || ContainsSelfRec1 g i
  ContainsSelfRec1 (f :.: g)  i = ContainsSelfRec1 f i || ContainsSelfRec1 g i

  -- this clause is a hack. If pieces @f@ is built from are not 'Generic1',
  -- this will get stuck.
  --
  -- An alternative with non-linear match is suboptimal in other ways
  ContainsSelfRec1 (Rec1 f)   i = ContainsSelfRec1 (Rep1 f) (i - 1)

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

type DefaultLog f = DefaultLog' (ContainsSelfRec1 (Rep1 f) 3) f
type DefaultTabulate f = DefaultTabulate' (ContainsSelfRec1 (Rep1 f) 3) f
type DefaultIndex f = DefaultIndex' (ContainsSelfRec1 (Rep1 f) 3) f

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
  type Log (Rec1 f) = Log f
  scatter k f = Rec1 #. scatter k (unRec1 #. f)
  index = index .# unRec1
  tabulate = Rec1 #. tabulate
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

instance (Distributive f, Distributive g) => Distributive (f :.: g) where
  type Log (f :.: g) = (Log f, Log g)
  scatter k phi wg = Comp1 $ scatter (scatter k coerce .# runAppCompose) id (AppCompose (ffmap phi wg))
  index (Comp1 f) (x, y) = index (index f x) y
  tabulate f = Comp1 $ tabulate $ \i -> tabulate $ \j -> f (i, j)
  {-# inline scatter #-}
  {-# inline tabulate #-}
  {-# inline index #-}

instance (Distributive f, Distributive g) => Distributive (Compose f g) where
  type Log (Compose f g) = Log (Rep1 (Compose f g))
  index = indexRep
  tabulate = tabulateRep
  {-# inline tabulate #-}
  {-# inline index #-}

instance (Distributive f, Distributive g) => Distributive (Product f g) where
  type Log (Product f g) = Log (Rep1 (Product f g))
  index = indexRep
  tabulate = tabulateRep
  {-# inline tabulate #-}

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

#if __GLASGOW_HASKELL__ >= 806
deriving newtype instance (Distributive f, Monad f) => Distributive (WrappedMonad f)
#else
instance (Distributive f, Monad f) => Distributive (WrappedMonad f) where
  type Log (WrappedMonad f) = Log f
  scatter k f = coerce $ scatter k (unwrapMonad #. f)
  index = index .# unwrapMonad
  tabulate = WrapMonad #. tabulate
  {-# inline scatter #-}
  {-# inline tabulate #-}
  {-# inline index #-}
#endif

instance Distributive f => Distributive (Kleisli f a) where
  type Log (Kleisli f a) = (a, Log f)
  scatter k f = coerce $ scatter k ((Comp1 . runKleisli) #. f)
  tabulate = (Kleisli . unComp1) #. tabulate
  index = index .# (Comp1 . runKleisli)
  {-# inline scatter #-}
  {-# inline tabulate #-}
  {-# inline index #-}

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

deriving newtype instance Distributive f => Distributive (IdentityT f)

#if __GLASGOW_HASKELL__ >= 806

deriving via ((((->) e) :.: f) :: Type -> Type)
  instance Distributive f => Distributive (ReaderT e f)

#else

instance Distributive f => Distributive (ReaderT e f) where
  type Log (ReaderT e f) = (e, Log f)
  scatter k f = coerce $ scatter k ((Comp1 . runReaderT) #. f)
  tabulate = (ReaderT . unComp1) #. tabulate
  index = index .# (Comp1 . runReaderT)
  {-# inline scatter #-}
  {-# inline tabulate #-}
  {-# inline index #-}

#endif

-- * DerivingVia

-- | Provides defaults definitions for other classes in terms of
-- 'Distributive'. Supplied for use with @DerivingVia@ in GHC 8.6+
--
-- Deriving 'Distributive', 'Foldable', or 'Traversable' via 'Dist' f leads to non-termination
-- but all other instances are fine for use and are defined in terms of these three.
newtype Dist f a = Dist { runDist :: f a }
  deriving stock (Foldable, Traversable)

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
  liftA2 = liftD2
  {-# inline liftA2 #-}

-- | A default definition for 'fmap' from 'Functor' in terms of 'Distributive'
fmapDist :: Distributive f => (a -> b) -> f a -> f b
fmapDist f fa = distrib (Element fa) $ \(Element a) -> coerce f a
{-# inline fmapDist #-}

-- | A default definition for 'pure' from 'Applicative' in terms of 'Distributive'
pureDist :: Distributive f => a -> f a
pureDist = tabulate . const
{-# inline pureDist #-}

-- | A default definition for '(<*>)' from 'Applicative' in terms of 'Distributive'
apDist :: Distributive f => f (a -> b) -> f a -> f b
apDist fab fa = distrib (D2 fab fa) $ \(D2 ab a) -> coerce ab a
{-# inline apDist #-}

-- | A default definition 'liftA2' from 'Applicative' in terms of 'Distributive'
liftD2 :: Distributive f => (a -> b -> c) -> f a -> f b -> f c
liftD2 f fa fb = distrib (D2 fa fb) $ \(D2 a b) -> coerce f a b
{-# inline liftD2 #-}

-- | An implementation of 'liftA3' in terms of 'Distributive'.
liftD3 :: Distributive f => (a -> b -> c -> d) -> f a -> f b -> f c -> f d
liftD3 f fa fb fc = distrib (D3 fa fb fc) $ \(D3 a b c) -> coerce f a b c
{-# inline liftD3 #-}

-- | An implementation of 'liftA4' in terms of 'Distributive'.
liftD4 :: Distributive f => (a -> b -> c -> d -> e) -> f a -> f b -> f c -> f d -> f e
liftD4 f fa fb fc fd = distrib (D4 fa fb fc fd) $ \(D4 a b c d) -> coerce f a b c d
{-# inline liftD4 #-}

-- | An implementation of 'liftA5' in terms of 'Distributive'.
liftD5 :: Distributive f => (a -> b -> c -> d -> e -> x) -> f a -> f b -> f c -> f d -> f e -> f x
liftD5 f fa fb fc fd fe = distrib (D5 fa fb fc fd fe) $ \(D5 a b c d e) -> coerce f a b c d e
{-# inline liftD5 #-}

-- * Monad

instance Distributive f => Monad (Dist f) where
  (>>=) = bindDist
  {-# inline (>>=) #-}

-- | A default implementation of '(>>=)' in terms of 'Distributive'
bindDist :: Distributive f => f a -> (a -> f b) -> f b
bindDist m f = distrib (DBind m f) $ \(DBind a f') -> coerce f' a
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

instance (Distributive f, Num a) => Num (Dist f a) where
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

instance (Distributive f, Fractional a) => Fractional (Dist f a) where
  (/) = liftA2 (/)
  recip = fmap recip
  fromRational = pure . fromRational
  {-# inline (/) #-}
  {-# inline recip #-}
  {-# inline fromRational #-}

instance (Distributive f, Floating a) => Floating (Dist f a) where
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

instance (Distributive f, Foldable f, Eq a) => Eq (Dist f a) where
  xs == ys = Monoid.getAll $ fold $ liftA2 (\x y -> Monoid.All (x == y)) xs ys
  {-# inline (==) #-}
  xs /= ys = Monoid.getAny $ fold $ liftA2 (\x y -> Monoid.Any (x /= y)) xs ys
  {-# inline (/=) #-}

instance (Distributive f, Foldable f, Ord a) => Ord (Dist f a) where
  compare xs ys = fold $ liftA2 compare xs ys
  {-# inline compare #-}

instance (Distributive f, Foldable f) => Eq1 (Dist f) where
  liftEq f xs ys = Monoid.getAll $ fold $ liftA2 (\x y -> Monoid.All (f x y)) xs ys
  {-# inline liftEq #-}

instance (Distributive f, Foldable f) => Ord1 (Dist f) where
  liftCompare f xs ys = fold $ liftA2 f xs ys
  {-# inline liftCompare #-}

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
{-# inline imapDist #-}

-- * FoldableWithIndex

-- | A default definition for 'ifoldMap' from @FoldableWithIndex@ in terms of 'Distributive'
ifoldMapDist
  :: forall f m a.
     (Distributive f, Foldable f, Monoid m)
  => (Log f -> a -> m) -> f a -> m
ifoldMapDist ix xs = fold (tabulate (\i -> ix i $ index xs i) :: f m)
{-# inline ifoldMapDist #-}

-- * TraversableWithIndex

-- | A default definition for 'itraverse' from @TraversableWithIndex@ in terms of 'Distributive'
itraverseDist
  :: forall f m a b.
     (Distributive f, Traversable f, Applicative m)
  => (Log f -> a -> m b) -> f a -> m (f b)
itraverseDist ix xs = sequenceA $ tabulate (ix <*> index xs)
{-# inline itraverseDist #-}

leftAdjunctDist :: Distributive u => ((a, Log u) -> b) -> a -> u b
leftAdjunctDist f a = tabulate (\s -> f (a,s))
{-# inline leftAdjunctDist #-}

rightAdjunctDist :: Distributive u => (a -> u b) -> (a, Log u) -> b
rightAdjunctDist f ~(a, k) = f a `index` k
{-# inline rightAdjunctDist #-}

data Path = End | L Path | R Path deriving (Eq, Ord, Show, Read)

-- This is not a legal 'Applicative', but it is used towards legal ends.

newtype Trail a = Trail { runTrail :: (Path -> Path) -> a }
  deriving Functor

instance Applicative Trail where
  pure = Trail . const
  {-# inline pure #-}
  fab <*> fa = Trail $ \k -> runTrail fab (k . L) $ runTrail fa (k . R)
  {-# inline (<*>) #-}

end :: Trail Path
end = Trail $ \k -> k End
{-# inline end #-}

logPath :: (Distributive f, Traversable f) => Logarithm f -> Path
logPath (Logarithm f) = f $ runTrail (traverse id $ pureDist end) id
{-# inline logPath #-}

-- unfortunate orphans, caused by having @hkd@ export the data type
-- rather than making it up here.
instance (Distributive f, Traversable f) => Eq (Logarithm f) where
  (==) = on (==) logPath
  {-# inline (==) #-}

instance (Distributive f, Traversable f) => Ord (Logarithm f) where
  (<) = on (<) logPath
  (<=) = on (<=) logPath
  (>=) = on (>=) logPath
  (>) = on (>) logPath
  compare = on compare logPath
  {-# inline compare #-}
  {-# inline (<) #-}
  {-# inline (<=) #-}
  {-# inline (>=) #-}
  {-# inline (>) #-}

type Lens' s a = forall f. Functor f => (a -> f a) -> s -> f s

-- This is also not a legal 'Applicative', but it is used towards legal ends.

data Evil a = Evil a (Path -> a)
  deriving Functor

instance Applicative Evil where
  pure a = Evil a $ \_ -> a
  {-# inline pure #-}
  ~(Evil mb mg) <*> ~(Evil nb ng) = Evil (mb nb) $ \case
    L xs -> mg xs nb
    R xs -> mb (ng xs)
    End -> undefined
  {-# inline (<*>) #-}

runEvil :: Evil a -> Path -> a
runEvil (Evil _ mg) p = mg p
{-# inline runEvil #-}

-- | For any 'Traversable', each logarithm identifies a 'Lens'.
_logarithm :: Traversable f => Logarithm f -> Lens' (f a) a
_logarithm (Logarithm f) a2ga fa = case f $ runTrail (traverse (\a -> (a,) <$> end) fa) id of
  (a, p) -> a2ga a <&> \a' -> runEvil (traverse (\a'' -> Evil a'' (const a')) fa) p
{-# inline _logarithm #-}

-- | We can convert a 'Logarithm' of a 'Distributive' functor to any choice of 'Log', as the two forms are canonically isomorphic.
--
-- @
-- 'index' f . 'logFromLogarithm' ≡ 'indexLogarithm' f
-- 'tabulate' (f . 'logFromLogarithm') ≡ 'tabulateLogarithm' f
-- 'logFromLogarithm' '.' 'logToLogarithm' ≡ 'id'
-- 'logToLogarithm' '.' 'logFromLogarithm' ≡ 'id'
-- @
logFromLogarithm :: Distributive f => Logarithm f -> Log f
logFromLogarithm (Logarithm f) = f askDist
{-# inline logFromLogarithm #-}

-- | We can convert any 'Log' to a 'Logarithm' as the two types are canonically isomorphic.
--
-- @
-- 'indexLogarithm' f . 'logToLogarithm' ≡ 'index' f
-- 'tabulateLogarithm' (f . 'logToLogarithm') ≡ 'tabulate' f
-- 'logFromLogarithm' '.' 'logToLogarithm' ≡ 'id'
-- 'logToLogarithm' '.' 'logFromLogarithm' ≡ 'id'
-- @
logToLogarithm :: Distributive f => Log f -> Logarithm f
logToLogarithm f = Logarithm (traceDist f)
{-# inline logToLogarithm #-}

-- | For any 'Traversable' 'Distributive' each 'Log' determines a 'Lens'.
_log :: (Traversable f, Distributive f) => Log f -> Lens' (f a) a
_log f = _logarithm (logToLogarithm f)
{-# inline _log #-}

_logEq :: (Distributive f, Eq (Log f)) => Log f -> Lens' (f a) a
_logEq i a2ga fa = a2ga (index fa i) <&> \a' -> imapDist (\j a -> if i == j then a' else a) fa
{-# inline _logEq #-}

{-
data Stream a = a :- Stream a
  deriving stock (Functor, Foldable, Traversable, Generic, Generic1, Show)
  deriving anyclass Distributive
  deriving ( Eq1, Ord1
           , Applicative
           , Monad, MonadFix, MonadZip, MonadReader (Logarithm Stream)
           ) via Dist Stream
  deriving ( Eq, Ord, Num, Fractional, Floating ) via Dist Stream a
infixr 5 :-
-}
