{-# Language CPP #-}
{-# Language AllowAmbiguousTypes #-}
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
{-# Language RoleAnnotations #-}
{-# Language ScopedTypeVariables #-}
{-# Language StandaloneDeriving #-}
{-# Language Trustworthy #-}
{-# Language TupleSections #-}
{-# Language TypeApplications #-}
{-# Language TypeFamilies #-}
{-# Language TypeOperators #-}
{-# Language UndecidableInstances #-}
{-# Language UndecidableSuperClasses #-}
{-# Language ViewPatterns #-}
{-# OPTIONS_GHC -Wno-orphans #-}

#ifndef MIN_VERSION_base
#define MIN_VERSION_base(_x,_y,_z) 1
#endif

-- |
-- Module      : Data.Distributive
-- Copyright   : (C) 2011-2021 Edward Kmett,
--               (c) 2017-2021 Aaron Vargo,
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
--   deriving stock (Eq, Ord, Functor, Foldable, Traversable, Generic, Generic1, Data)
--   deriving anyclass Distributive
--   deriving ( Applicative, Monad, MonadFix, MonadZip
--              MonadReader (Logarithm V3)
--            , FunctorWithIndex (Logarithm V3)
--            , FoldableWithIndex (Logarithm V3)
--            , TraversableWithIndex (Logarithm V3)
--            , Eq1, Ord1
--            ) via Dist V3
--   deriving (Num, Fractional, Floating) via Dist V3 a
-- @
--
-- If you want a special form for the 'Log' of your functor you can
-- implement tabulate and index directly, `Dist` can still be used.
module Data.Distributive
( Distributive(..)
, distribute
, distrib
, dist
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
, eqLog
, neLog
, gtLog
, geLog
, ltLog
, leLog
, compareLog
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
, localDist
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
-- * Eq/Eq1
, eqDist
, neDist
, liftEqDist
-- * Ord/Ord1
, compareDist
, liftCompareDist
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
import Data.Distributive.Coerce
import Data.Distributive.Util
import Data.Distributive.Internal.Orphans ()
import Data.Foldable (fold)
import Data.Foldable.WithIndex
import Data.Function (on)
import Data.Functor.Classes
import Data.Functor.Compose
import Data.Functor.Identity
import Data.Functor.Product
import Data.Functor.Reverse
import Data.Functor.WithIndex
import Data.Kind
import qualified Data.Monoid as Monoid
import qualified Data.Semigroup as Semigroup
import Data.HKD
import Data.Ord (Down(..))
import Data.Orphans ()
import Data.Proxy
import Data.Traversable.WithIndex
import Data.Void
import GHC.Generics
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

  -- | Defaults to 'tabulateLogarithm' when @'Log' f = 'Logarithm' f@, otherwise to 'tabulateRep'
  tabulate :: (Log f -> a) -> f a
  default tabulate :: DefaultTabulate f => (Log f -> a) -> f a
  tabulate = defaultTabulate
  {-# inline tabulate #-}

  -- | Defaults to 'indexLogarithm' when @'Log' f = 'Logarithm' f@, otherwise to 'indexRep'
  index :: f a -> Log f -> a
  default index :: DefaultIndex f => f a -> Log f -> a
  index = defaultIndex
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
scatterRep = \k phi -> to1 . scatter k (from1 . phi)
{-# inline scatterRep #-}

pattern Tabulate :: Distributive f => (Log f -> a) -> f a
pattern Tabulate i <- (index -> i) where
  Tabulate i = tabulate i

-- * Generic derivation

type family DefaultLog' (containsRec1 :: Bool) f :: Type where
  DefaultLog' 'True  f = Logarithm f
  DefaultLog' 'False f = Log (Rep1 f)

type DefaultLog f = DefaultLog' (ContainsSelfRec1 (Rep1 f) 3) f

type family IsLogarithm f t :: Bool where
  IsLogarithm f (Logarithm f) = 'True
  IsLogarithm f t = 'False

type LogIsLogarithm f = IsLogarithm f (Log f)

type family DefaultImplC (logIsLogarithm :: Bool) f :: Constraint where
  DefaultImplC 'True  f = (Distributive f, Log f ~ Logarithm f)
  DefaultImplC 'False f = (Generic1 f, Distributive (Rep1 f), Coercible (Log f) (Log (Rep1 f)))

-- individual type classes, so GHC needs to do less work
class DefaultImplC logIsLogarithm f => DefaultTabulate' (logIsLogarithm :: Bool) f where
  defaultTabulate' :: (Log f -> a) -> f a

instance DefaultImplC 'True f => DefaultTabulate' 'True f where
  defaultTabulate' = tabulateLogarithm
  {-# inline defaultTabulate' #-}

instance DefaultImplC 'False f => DefaultTabulate' 'False f where
  defaultTabulate' = tabulateRep
  {-# inline defaultTabulate' #-}

type DefaultTabulate f = DefaultTabulate' (LogIsLogarithm f) f

defaultTabulate :: forall f a. DefaultTabulate f => (Log f -> a) -> f a
defaultTabulate = defaultTabulate' @(LogIsLogarithm f)
{-# inline defaultTabulate #-}

class DefaultImplC logIsLogarithm f => DefaultIndex' (logIsLogarithm :: Bool) f where
  defaultIndex' :: f a -> Log f -> a

instance DefaultImplC 'True f => DefaultIndex' 'True f where
  defaultIndex' = indexLogarithm
  {-# inline defaultIndex' #-}

instance DefaultImplC 'False f => DefaultIndex' 'False f where
  defaultIndex' = indexRep
  {-# inline defaultIndex' #-}

type DefaultIndex f = DefaultIndex' (LogIsLogarithm f) f

defaultIndex :: forall f a. DefaultIndex f => f a -> (Log f -> a)
defaultIndex = defaultIndex' @(LogIsLogarithm f)
{-# inline defaultIndex #-}

-- | A helper for the most common usage pattern when working with higher-kinded data.
--
-- @
-- 'distrib' w k ≡ 'scatter' k id w
-- @
distrib :: (Distributive f, FFunctor w) => w f -> (w Identity -> r) -> f r
distrib = \ w k -> scatter k id w
{-# inline distrib #-}

-- | The essential essence of the new 'scatter' with administrative mapping removed.
dist :: (Distributive f, FFunctor w) => w f -> f (w Identity)
dist = scatter id id
{-# inline dist #-}

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
scatterDefault = \k phi wg ->
  tabulate $ \x -> k $ ffmap (\g -> Identity $ index (phi g) x) wg
{-# inline scatterDefault #-}

-- | Default definition for 'tabulate' when @'Log' f@ = @'Logarithm' f@. Can be used
-- to manipulate 'Logarithm's regardless of the choice of 'Log' for your distributive
-- functor.
tabulateLogarithm :: Distributive f => (Logarithm f -> a) -> f a
tabulateLogarithm = \ f ->
  distrib (Tab f) $ \(Tab f') -> f' (Logarithm runIdentity)
{-# inline tabulateLogarithm #-}

-- | @'Logarithm' f = f ~> 'Identity'@
--
-- When @f@ is 'Distributive', this is the representation/logarithm of @f@, up to isomorphism. i.e.
--
-- @f a ≅ Logarithm f -> a@
--
-- Consider the case where @f = (->) r@. It follows from the yoneda lemma that
--
-- @(->) r '~>' 'Identity' ≅ r@
--
-- i.e. we have
--
-- @'Logarithm' ((->) r) = forall a. (r -> a) -> a ≅ r@
--
-- This works more generally for any 'Distributive' functor. E.g. given
--
-- @data V2 a = V2 a a@
--
-- we have
--
-- @
-- V2 a ≅ Bool -> a
-- 'Logarithm' V2 ≅ Bool
-- @
type role Logarithm representational
newtype Logarithm f = Logarithm { runLogarithm :: forall a. f a -> a }

indexLogarithm :: f a -> Logarithm f -> a
indexLogarithm = \fa (Logarithm fa2a) -> fa2a fa
{-# inline indexLogarithm #-}

instance FContravariant Logarithm where
  fcontramap = \f g -> Logarithm (runLogarithm g . f)
  {-# inline fcontramap #-}

-- | Tabulation.
newtype Tab a f = Tab { runTab :: Logarithm f -> a }

instance FFunctor (Tab a) where
  ffmap = \ f g -> Tab (runTab g . fcontramap f)
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
distribute = \f -> distrib (DCompose f) $ \(DCompose f') -> runIdentity <$> f'
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
collect = \ f fa -> distrib (DCompose f) $ \(DCompose f') -> coerce f' <$> fa
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
cotraverse = \fab fga ->
  distrib (DCompose fga) $ \(DCompose f') -> fab (runIdentity <$> f')
{-# inline cotraverse #-}


instance (Distributive f, Distributive g) => Distributive (f :*: g) where
  type Log (f :*: g) = Either (Log f) (Log g)
  scatter = \ k f (ffmap f -> w) ->
        scatter k (\(l :*: _) -> l) w
    :*: scatter k (\(_ :*: r) -> r) w
  tabulate = \ f -> tabulate (f . Left) :*: tabulate (f . Right)
  index = \(f :*: g) -> \case
    Left x -> index f x
    Right y -> index g y
  {-# inline scatter #-}
  {-# inline tabulate #-}
  {-# inline index #-}

instance Distributive f => Distributive (M1 i c f) where
  type Log (M1 i c f) = Log f
  scatter = \k f -> M1 #. scatter k (unM1 #. f)
  index = index .# unM1
  tabulate = M1 #. tabulate
  {-# inline scatter #-}
  {-# inline tabulate #-}
  {-# inline index #-}

instance Distributive U1 where
  type Log U1 = Void
  scatter = \_ _ _ -> U1
  tabulate = \_ -> U1
  index = \_ -> absurd
  {-# inline scatter #-}
  {-# inline tabulate #-}
  {-# inline index #-}

instance Distributive f => Distributive (Rec1 f) where
  type Log (Rec1 f) = Log f
  scatter = \ k f -> Rec1 #. scatter k (unRec1 #. f)
  index = index .# unRec1
  tabulate = Rec1 #. tabulate
  {-# inline scatter #-}
  {-# inline tabulate #-}
  {-# inline index #-}

instance Distributive Par1 where
  type Log Par1 = ()
  scatter = \k f -> coerce $ k .  ffmap ((Identity . unPar1) #. f)
  index = \x _ -> unPar1 x
  tabulate = \f -> Par1 $ f ()
  {-# inline scatter #-}
  {-# inline tabulate #-}
  {-# inline index #-}

instance (Distributive f, Distributive g) => Distributive (f :.: g) where
  type Log (f :.: g) = (Log f, Log g)
  scatter = \ k phi wg -> Comp1 $ scatter (scatter k coerce .# runAppCompose) id (AppCompose (ffmap phi wg))
  index = \ (Comp1 f) (x, y) -> index (index f x) y
  tabulate = \f -> Comp1 $ tabulate $ \i -> tabulate $ \j -> f (i, j)
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
  {-# inline index #-}

instance Distributive Proxy
instance Distributive Identity

instance Distributive ((->) x) where
  type Log ((->) x) = x
  scatter = \ k phi wg x -> k $ ffmap (\g -> Identity $ phi g x) wg
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
  scatter = \k f -> coerce $ k . ffmap ((Identity . getDown) #. f)
  index = \x _ -> getDown x
  tabulate = \f -> Down $ f ()
  {-# inline scatter #-}
  {-# inline tabulate #-}
  {-# inline index #-}

instance Distributive Monoid.Product where
  type Log Monoid.Product = ()
  scatter = \k f -> coerce $ k .  ffmap ((Identity . Monoid.getProduct) #. f)
  index = \x _ -> Monoid.getProduct x
  tabulate = \f -> Monoid.Product $ f ()
  {-# inline scatter #-}
  {-# inline tabulate #-}
  {-# inline index #-}

instance Distributive Monoid.Sum where
  type Log Monoid.Sum = ()
  scatter = \ k f -> coerce $ (k .  ffmap ((Identity . Monoid.getSum) #. f))
  index = \ x _ -> Monoid.getSum x
  tabulate = \f -> Monoid.Sum $ f ()
  {-# inline scatter #-}
  {-# inline tabulate #-}
  {-# inline index #-}

#endif

deriving newtype instance Distributive f => Distributive (Backwards f)
deriving newtype instance Distributive f => Distributive (Reverse f)
deriving newtype instance Distributive f => Distributive (Monoid.Alt f)
instance Distributive Monoid.Dual

#if MIN_VERSION_base(4,12,0)

deriving newtype instance Distributive f => Distributive (Monoid.Ap f)

#endif

instance Distributive Semigroup.First
instance Distributive Semigroup.Last
instance Distributive Semigroup.Min
instance Distributive Semigroup.Max

deriving newtype instance (Distributive f, Monad f) => Distributive (WrappedMonad f)

instance Distributive f => Distributive (Kleisli f a) where
  type Log (Kleisli f a) = (a, Log f)
  scatter = \k f -> coerce $ scatter k ((Comp1 . runKleisli) #. f)
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
  tabulate = \ f -> f False :+ f True
  {-# inline tabulate #-}
  index = \ (r :+ i) -> \case
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
  scatter = \ k f -> coerce $ scatter k ((Comp1 . runReaderT) #. f)
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

type role Dist representational nominal
newtype Dist f a = Dist { runDist :: f a }
  deriving stock (Foldable, Traversable)

instance Distributive f => Functor (Dist f) where
  fmap = fmapDist
  {-# inline fmap #-}
  (<$) = const . pure
  {-# inline (<$) #-}

-- | A default definition for 'fmap' from 'Functor' in terms of 'Distributive'
fmapDist :: Distributive f => (a -> b) -> f a -> f b
fmapDist = \ f fa -> distrib (Element fa) $ \(Element a) -> coerce f a
{-# inline fmapDist #-}

instance Distributive f => Distributive (Dist f) where
  type Log (Dist f) = Log f
  scatter = \ k f -> Dist #. scatter k (runDist #. f)
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

-- | A default definition for 'pure' from 'Applicative' in terms of 'Distributive'
pureDist :: Distributive f => a -> f a
pureDist = scatter getConst id .# Const
-- pureDist = distrib Proxy . const
{-# inline pureDist #-}

-- | A default definition for '(<*>)' from 'Applicative' in terms of 'Distributive'
apDist :: Distributive f => f (a -> b) -> f a -> f b
apDist = \fab fa ->
  distrib (D2 fab fa) $ \(D2 ab a) -> coerce ab a
{-# inline apDist #-}

-- | A default definition 'liftA2' from 'Applicative' in terms of 'Distributive'
liftD2 :: Distributive f => (a -> b -> c) -> f a -> f b -> f c
liftD2 = \f fa fb ->
  distrib (D2 fa fb) $ \(D2 a b) -> coerce f a b
{-# inline liftD2 #-}

-- | An implementation of 'liftA3' in terms of 'Distributive'.
liftD3 :: Distributive f => (a -> b -> c -> d) -> f a -> f b -> f c -> f d
liftD3 = \ f fa fb fc ->
  distrib (D3 fa fb fc) $ \(D3 a b c) -> coerce f a b c
{-# inline liftD3 #-}

-- | An implementation of 'liftA4' in terms of 'Distributive'.
liftD4 :: Distributive f => (a -> b -> c -> d -> e) -> f a -> f b -> f c -> f d -> f e
liftD4 = \f fa fb fc fd ->
  distrib (D4 fa fb fc fd) $ \(D4 a b c d) -> coerce f a b c d
{-# inline liftD4 #-}

-- | An implementation of 'liftA5' in terms of 'Distributive'.
liftD5 :: Distributive f => (a -> b -> c -> d -> e -> x) -> f a -> f b -> f c -> f d -> f e -> f x
liftD5 = \f fa fb fc fd fe ->
  distrib (D5 fa fb fc fd fe) $ \(D5 a b c d e) -> coerce f a b c d e
{-# inline liftD5 #-}

-- * Monad

instance Distributive f => Monad (Dist f) where
  (>>=) = bindDist
  {-# inline (>>=) #-}

-- | A default implementation of '(>>=)' in terms of 'Distributive'
bindDist :: Distributive f => f a -> (a -> f b) -> f b
bindDist = \ m f -> distrib (DBind m f) $ \(DBind a f') -> coerce f' a
{-# inline bindDist #-}

-- * MonadFix

instance Distributive f => MonadFix (Dist f) where
  mfix = mfixDist
  {-# inline mfix #-}

-- | A default definition for 'mfix' in terms of 'Distributive'
mfixDist :: Distributive f => (a -> f a) -> f a
mfixDist = \ama -> distrib (DCompose ama) (fix . coerce)
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

instance (Distributive f, Semigroup a) => Semigroup (Dist f a) where
  (<>) = liftD2 (<>)
  {-# inline (<>) #-}

instance (Distributive f, Monoid a) => Monoid (Dist f a) where
  mempty = pure mempty
  {-# noinline[0] mempty #-}
#if !(MIN_VERSION_base(4,11,0))
  mappend = liftD2 mappend
  {-# inline mappend #-}
#endif

instance (Distributive f, Foldable f, Eq a) => Eq (Dist f a) where
  (==) = eqDist
  {-# inline (==) #-}
  (/=) = neDist
  {-# inline (/=) #-}

eqDist
  :: (Distributive f, Foldable f, Eq a)
  => f a -> f a -> Bool
eqDist = \ xs ys ->
  Monoid.getAll $ fold $ liftD2 (\x y -> Monoid.All (x == y)) xs ys
{-# inline eqDist #-}

neDist
  :: (Distributive f, Foldable f, Eq a)
  => f a -> f a -> Bool
neDist = \ xs ys ->
  Monoid.getAny $ fold $ liftD2 (\x y -> Monoid.Any (x /= y)) xs ys

instance (Distributive f, Foldable f, Ord a) => Ord (Dist f a) where
  compare = \xs ys -> fold $ liftD2 compare xs ys
  {-# inline compare #-}

compareDist
  :: (Distributive f, Foldable f, Ord a)
  => f a -> f a -> Ordering
compareDist = \xs ys -> fold $ liftD2 compare xs ys
{-# inline compareDist #-}

liftCompareDist
  :: (Distributive f, Foldable f)
  => (a -> b -> Ordering)
  -> f a -> f b -> Ordering
liftCompareDist = \f xs ys -> fold $ liftD2 f xs ys
{-# inline liftCompareDist #-}

liftEqDist :: (Distributive f, Foldable f) => (a -> b -> Bool) -> f a -> f b -> Bool
liftEqDist = \f xs ys ->
  Monoid.getAll $ fold $ liftD2 (\x y -> Monoid.All (f x y)) xs ys
{-# inline liftEqDist #-}

instance (Distributive f, Foldable f) => Eq1 (Dist f) where
  liftEq = liftEqDist
  {-# inline liftEq #-}

instance (Distributive f, Foldable f) => Ord1 (Dist f) where
  liftCompare = liftCompareDist
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
extendDist = \f g -> tabulate $ \i -> f $ tabulate $ \j -> index g (i <> j)
{-# inline extendDist #-}

-- | A default definition for 'duplicate' from @Comonad@ in terms of 'Distributive'
duplicateDist :: (Distributive f, Semigroup (Log f)) => f a -> f (f a)
duplicateDist = \f -> tabulate $ \i -> tabulate $ \j -> index f (i <> j)
{-# inline duplicateDist #-}

-- | A default definition for 'extract' from @Comonad@ in terms of 'Distributive'
-- where the user chooses to supply a 'unit' logarithm other than 'mempty'
extractDistBy :: Distributive f => Log f -> f a -> a
extractDistBy = flip index
{-# inline extractDistBy #-}

-- | A default definition for 'extend' from @Comonad@ in terms of 'Distributive'
-- where the user chooses to supply a semigroup on logarithms other than '<>'
extendDistBy :: Distributive f => (Log f -> Log f -> Log f) -> (f a -> b) -> f a -> f b
extendDistBy = \t f g -> tabulate $ \i -> f $ tabulate $ \j -> index g (t i j)

{-# inline extendDistBy #-}
-- | A default definition for 'duplicate' from @Comonad@ in terms of 'Distributive'
-- where the user chooses to supply an semigroup on logarithms other than '<>'
duplicateDistBy :: Distributive f => (Log f -> Log f -> Log f) -> f a -> f (f a)
duplicateDistBy = \t f -> tabulate $ \i -> tabulate $ \j -> index f (t i j)
{-# inline duplicateDistBy #-}

-- * MonadReader

-- deriving via (f :.: ((->) e)) instance Distributive f => Distributive (TracedT e f)

-- | A default definition for 'ask' from 'MonadReader' in terms of 'Distributive'
askDist :: Distributive f => f (Log f)
askDist = tabulate id
{-# noinline[0] askDist #-}

-- | A default definition for 'local' from 'MonadReader' in terms of 'Distributive'
localDist :: Distributive f => (Log f -> Log f) -> f a -> f a
localDist = \f m -> tabulate (index m . f)
{-# inline localDist #-}

-- * ComonadTrace

-- | A default definition for 'trace' from @ComonadTrace@ in terms of 'Distributive'
traceDist :: Distributive f => Log f -> f a -> a
traceDist = flip index
{-# inline traceDist #-}

-- * FunctorWithIndex

instance (Distributive f, Log f ~ i) => FunctorWithIndex i (Dist f) where
  imap = imapDist
  {-# inline imap #-}

-- | A default definition for 'imap' from @FunctorWithIndex@ in terms of 'Distributive'
imapDist
  :: Distributive f
  => (Log f -> a -> b) -> f a -> f b
imapDist = \f xs -> tabulate (f <*> index xs)
{-# inline imapDist #-}

-- * FoldableWithIndex

instance (Distributive f, Foldable f, Log f ~ i) => FoldableWithIndex i (Dist f) where
  ifoldMap = ifoldMapDist
  {-# inline ifoldMap #-}

-- | A default definition for 'ifoldMap' from @FoldableWithIndex@ in terms of 'Distributive'
ifoldMapDist
  :: forall f m a.
     (Distributive f, Foldable f, Monoid m)
  => (Log f -> a -> m) -> f a -> m
ifoldMapDist = \ix xs -> fold (tabulate (\i -> ix i $ index xs i) :: f m)
{-# inline ifoldMapDist #-}

-- * TraversableWithIndex

instance (Distributive f, Traversable f, Log f ~ i) => TraversableWithIndex i (Dist f) where
  itraverse = itraverseDist
  {-# inline itraverse #-}

-- | A default definition for 'itraverse' from @TraversableWithIndex@ in terms of 'Distributive'
itraverseDist
  :: forall f m a b.
     (Distributive f, Traversable f, Applicative m)
  => (Log f -> a -> m b) -> f a -> m (f b)
itraverseDist = \ix xs -> sequenceA $ tabulate (ix <*> index xs)
{-# inline itraverseDist #-}

leftAdjunctDist :: Distributive u => ((a, Log u) -> b) -> a -> u b
leftAdjunctDist = \f a -> tabulate (\s -> f (a,s))
{-# inline leftAdjunctDist #-}

rightAdjunctDist :: Distributive u => (a -> u b) -> (a, Log u) -> b
rightAdjunctDist = \f ~(a, k) -> f a `index` k
{-# inline rightAdjunctDist #-}

logarithmPath :: (Distributive f, Traversable f) => Logarithm f -> Path
logarithmPath = \ f -> runLogarithm f $ runTrail (traverse id $ pureDist end) id
{-# inline logarithmPath #-}

-- AllowAmbiguousTypes?
--logPath :: forall f. (Distributive f, Traversable f) => Proxy f -> Log f -> Path
--logPath = \ _ f -> index (runTrail (traverse id $ pureDist end) id :: f Path) f
logPath :: forall f. (Distributive f, Traversable f) => Log f -> Path
logPath = index (runTrail (traverse id $ pureDist @f end) id)
{-# inline logPath #-}

-- unfortunate orphans, caused by having @hkd@ export the data type
-- rather than making it up here.
instance (Distributive f, Traversable f) => Eq (Logarithm f) where
  (==) = on (==) logarithmPath
  {-# inline (==) #-}

instance (Distributive f, Traversable f) => Ord (Logarithm f) where
  (<) = on (<) logarithmPath
  (<=) = on (<=) logarithmPath
  (>=) = on (>=) logarithmPath
  (>) = on (>) logarithmPath
  compare = on compare logarithmPath
  {-# inline compare #-}
  {-# inline (<) #-}
  {-# inline (<=) #-}
  {-# inline (>=) #-}
  {-# inline (>) #-}

-- | Use explicit type application to call this function. e.g. @'eqLog' \@f@
--
-- Compare two logarithms for equality
eqLog :: forall f. (Distributive f, Traversable f) => Log f -> Log f -> Bool
eqLog = on (==) (logPath @f)

-- | Use explicit type application to call this function. e.g. @'neLog' \@f@
--
-- Compare two logarithms for disequality
neLog :: forall f. (Distributive f, Traversable f) => Log f -> Log f -> Bool
neLog = on (/=) (logPath @f)

-- | Use explicit type application to call this function. e.g. @'ltLog' \@f@
ltLog :: forall f. (Distributive f, Traversable f) => Log f -> Log f -> Bool
ltLog = on (<) (logPath @f)

-- | Use explicit type application to call this function. e.g. @'leLog' \@f@
leLog :: forall f. (Distributive f, Traversable f) => Log f -> Log f -> Bool
leLog = on (<=) (logPath @f)

-- | Use explicit type application to call this function. e.g. @'gtLog' \@f@
gtLog :: forall f. (Distributive f, Traversable f) => Log f -> Log f -> Bool
gtLog = on (>) (logPath @f)

-- | Use explicit type application to call this function. e.g. @'geLog' \@f@
geLog :: forall f. (Distributive f, Traversable f) => Log f -> Log f -> Bool
geLog = on (>=) (logPath @f)

-- | Use explicit type application to call this function. e.g. @'compareLog' \@f@
--
-- Compare two logarithms
compareLog :: forall f. (Distributive f, Traversable f) => Log f -> Log f -> Ordering
compareLog = on compare (logPath @f)

type Lens' s a = forall f. Functor f => (a -> f a) -> s -> f s

-- | For any 'Traversable', each logarithm identifies a 'Lens'.
_logarithm :: Traversable f => Logarithm f -> Lens' (f a) a
_logarithm = \(Logarithm f) a2ga fa ->
  case f $ runTrail (traverse (\a -> (a,) <$> end) fa) id of
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
logFromLogarithm = \(Logarithm f) -> f askDist
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
logToLogarithm = \f -> Logarithm (traceDist f)
{-# inline logToLogarithm #-}

-- | For any 'Traversable' 'Distributive' each 'Log' determines a 'Lens'.
--
-- @
-- '_log' f = '_logarithm' ('logToLogarithm' f)
-- @
_log :: (Traversable f, Distributive f) => Log f -> Lens' (f a) a
_log = \lg a2ga fa ->
  case index (runTrail (traverse (\a -> (a,) <$> end) fa) id) lg of
    (a, p) -> a2ga a <&> \a' -> runEvil (traverse (\a'' -> Evil a'' (const a')) fa) p
{-# inline _log #-}

-- | Construct the lens using @'Eq' ('Log' f)@ instead of with @'Traversable' f@
_logEq :: (Distributive f, Eq (Log f)) => Log f -> Lens' (f a) a
_logEq = \i a2ga fa -> a2ga (index fa i) <&> \a' -> imapDist (\j a -> if i == j then a' else a) fa
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
