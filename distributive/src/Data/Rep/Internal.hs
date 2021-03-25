{-# Language CPP #-}
{-# Language GeneralizedNewtypeDeriving #-}
{-# Language Unsafe #-}
{-# options_haddock not-home #-}

-- |
-- Copyright   : (C) 2011-2021 Edward Kmett,
--               (c) 2017-2021 Aaron Vargo,
--               (c) 2021 Oleg Grenrus
-- License     : BSD-2-Clause OR Apache-2.0
-- Maintainer  : Edward Kmett <ekmett@gmail.com>
-- Stability   : provisional
-- Portability : non-portable (ghc 8.6+)

module Data.Rep.Internal where

import Control.Applicative
import Control.Applicative.Backwards
import Control.Arrow
import Control.Monad.Fix
import Control.Monad.Reader
import Control.Monad.Trans.Identity
import Control.Monad.Zip
import Data.Coerce
import Data.Complex
import Data.Data
import Numeric.Fin.Internal
import Data.Function.Coerce
import Data.Foldable (fold)
import Data.Foldable.WithIndex
import Data.Function
import Data.Functor
import Data.Functor.Classes
import Data.Functor.Compose
import Data.Functor.Identity
import Data.Functor.Product
import Data.Functor.Reverse
import Data.Functor.WithIndex
import Data.GADT.Compare
import Data.HKD
import Data.HKD.Contravariant
import Data.HKD.Index.Internal
import Data.Kind
import Data.Maybe
import qualified Data.Monoid as Monoid
import Data.Ord (Down(..))
import Data.Orphans ()
import qualified Data.Semigroup as Semigroup
import Data.Some
import Data.Traversable
import Data.Traversable.WithIndex
import Data.Type.Bool
import Data.Type.Coercion
import Data.Type.Equality
import Data.Void
import GHC.Generics
import GHC.TypeLits
import Numeric
import Unsafe.Coerce

#ifdef MIN_VERSION_tagged
import Data.Tagged
#endif

#ifdef MIN_VERSION_comonad
import Control.Comonad
import Control.Comonad.Trans.Traced
#endif

-- |
--
-- Due to the lack of non-trivial comonoids in Haskell, we can restrict
-- ourselves to requiring a 'Functor' rather than some Coapplicative class.
-- Categorically every 'Representable' functor is actually a right adjoint,
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

class Indexable f where
  -- | Defaults to @'Log' ('Rep1' f)@ when @f@ is non-recursive, otherwise to 'Logarithm'.
  type Log f
  type Log f = DefaultLog f

  type KnownSize f :: Maybe Nat
  type KnownSize f = DefaultKnownSize f

  -- | Defaults to 'indexLogarithm' when @'Log' f = 'Logarithm' f@, otherwise to 'indexGeneric'
  index :: f a -> Log f -> a
  default index :: DefaultIndex f => f a -> Log f -> a
  index = defaultIndex
  {-# inline index #-}

class (Indexable f, Functor f) => Representable f where
  -- | Defaults to 'tabulateLogarithm' when @'Log' f = 'Logarithm' f@, otherwise to 'tabulateGeneric'
  tabulate :: (Log f -> a) -> f a
  default tabulate :: DefaultTabulate f => (Log f -> a) -> f a
  tabulate = defaultTabulate
  {-# inline tabulate #-}

  -- | Scatter the contents of an 'FFunctor'. This admittedly complicated operation
  -- is necessary to get asymptotically optimal performance for 'Representable' functors
  -- like Mealy and Moore machines that have many layers to them.
  --
  -- If you have a 'Generic1' instance for your 'Functor', this should be able to be
  -- generated automatically. Otherwise, if you must, you can use 'scatterDefault' as
  -- a fallback in terms of 'tabulate' and 'index', which is offered in terms of the
  -- law relating 'scatter' to 'tabulate' and 'index':
  --
  -- @
  -- 'scatter' phi wg ≡ 'tabulate' \\x -> 'ffmap' (\\g -> 'Identity' '$' 'index' (phi g) x) wg
  -- @
  --
  -- Defaults to 'scatterGeneric'
  --
  -- The obvious API for this function is the much simpler
  --
  -- @
  -- 'dist ':: ('Representable' f, 'FFunctor' w) => w f -> f (w 'Identity')
  -- @
  --
  -- However, most uses of this function aren't interested in leaving a @w 'Identity'@ inside @f@
  -- and immediately 'ffmap' to replace it. However, most implementations have to 'ffmap' to put
  -- it there. This leads to two unfused 'ffmap' calls. By adding a @(w 'Identity' -> r)@ step
  -- we clean up that concern.
  --
  -- Another concern with the obvious implementation as a class method is that 'w f' knows nothing
  -- about whether 'w' takes a representational argument. As a result, @GeneralizedNewtypeDeriving@
  -- wouldn't work for this class if this was a member. (For an example of this, try to use GND on
  -- 'Traversable' today!) Adding a natural transformation before we process allows this
  -- dictionary to be derived with GND. This latter mapping is a lot less useful, so we supply
  --
  -- @
  -- 'distrib' :: ('Representable' f, 'FFunctor' w) => w f -> (w 'Identity' -> r) -> f r
  -- @
  --
  -- as well, outside o the class, which is quite concise for many workloads.
  scatter :: FFunctor w => (w Identity -> r) -> (g ~> f) -> w g -> f r
  default scatter
    :: (Generic1 f, Representable (Rep1 f), FFunctor w)
    => (w Identity -> r) -> (g ~> f) -> w g -> f r
  scatter = scatterGeneric
  {-# inline scatter #-}

-- | derive tabulate via 'Generic1' when @'Log' f@ is (a possible newtype of)
-- @'Log' ('Rep1' f)@
tabulateGeneric
  :: forall f a.
     (Representable (Rep1 f), Generic1 f, Coercible (Log f) (Log (Rep1 f)))
  => (Log f -> a) -> f a
tabulateGeneric = coerce (to1 . tabulate :: (Log (Rep1 f) -> a) -> f a)
{-# inline tabulateGeneric #-}

-- | derive 'index' via 'Generic1' when @'Log' f@ is (a possible newtype of)
-- @'Log' ('Rep1' f)@
indexGeneric
  :: forall f a.
     (Indexable (Rep1 f), Generic1 f, Coercible (Log f) (Log (Rep1 f)))
  => f a -> Log f -> a
indexGeneric = coerce (index . from1 :: f a -> Log (Rep1 f) -> a)
{-# inline indexGeneric #-}

-- | derive 'scatter' via 'Generic1'
scatterGeneric
  :: (Representable (Rep1 f), Generic1 f, FFunctor w)
  => (w Identity -> r) -> (g ~> f) -> w g -> f r
scatterGeneric = \k phi -> to1 . scatter k (from1 . phi)
{-# inline scatterGeneric #-}

-- | This pattern synonym lets you work with any 'Representable' functor as if
-- it were a function.
pattern Tabulate :: Representable f => (Log f -> a) -> f a
pattern Tabulate i <- (index -> i) where
  Tabulate i = tabulate i

-- * Generic derivation

data LogType
  = UseLogarithm
  | UseLogFin
  | UseLogRep

type family HasLogType f t :: LogType where
  HasLogType f (Logarithm f) = 'UseLogarithm
  HasLogType f (Fin x) = If (x == Size f) 'UseLogFin 'UseLogRep
  HasLogType f t = 'UseLogRep

type LogTypeOf f = HasLogType f (Log f)

type DefaultLog f = DefaultLog' (GInvalid (Rep1 f)) f

type family DefaultLog' (containsRec1 :: Bool) f :: Type where
  DefaultLog' 'True  f = Logarithm f
  DefaultLog' 'False f = DefaultLog'' (GUnknownSize (Rep1 f)) f

type family DefaultLog'' (hasUnknownSize :: Bool) f :: Type where
  DefaultLog'' 'True f = Log (Rep1 f)
  DefaultLog'' 'False f = Fin (Size f)

type family DefaultTabulateImplC (t :: LogType) f :: Constraint where
  DefaultTabulateImplC 'UseLogarithm f = (Representable f, Log f ~ Logarithm f)
  DefaultTabulateImplC 'UseLogRep f = (Generic1 f, Representable (Rep1 f), Coercible (Log f) (Log (Rep1 f)))
  DefaultTabulateImplC 'UseLogFin f = (Generic1 f, GTabulateFin (Rep1 f), Size f ~ GSize (Rep1 f), Log f ~ Fin (GSize (Rep1 f)))

type family DefaultIndexImplC (t :: LogType) f :: Constraint where
  DefaultIndexImplC 'UseLogarithm f = (Log f ~ Logarithm f)
  DefaultIndexImplC 'UseLogRep f = (Generic1 f, Representable (Rep1 f), Coercible (Log f) (Log (Rep1 f)))
  DefaultIndexImplC 'UseLogFin f = (Generic1 f, GIndexFin (Rep1 f), Size f ~ GSize (Rep1 f), Log f ~ Fin (GSize (Rep1 f)))

-- individual type classes, so GHC needs to do less work
class DefaultTabulateImplC logType f => DefaultTabulate' (logType :: LogType) f where
  defaultTabulate' :: (Log f -> a) -> f a

instance DefaultTabulateImplC 'UseLogarithm f => DefaultTabulate' 'UseLogarithm f where
  defaultTabulate' = tabulateLogarithm
  {-# inline defaultTabulate' #-}

instance DefaultTabulateImplC 'UseLogRep f => DefaultTabulate' 'UseLogRep f where
  defaultTabulate' = tabulateGeneric
  {-# inline defaultTabulate' #-}

instance DefaultTabulateImplC 'UseLogFin f => DefaultTabulate' 'UseLogFin f where
  defaultTabulate' = gtabulateFin
  {-# inline defaultTabulate' #-}

type DefaultTabulate f = DefaultTabulate' (LogTypeOf f) f

defaultTabulate :: forall f a. DefaultTabulate f => (Log f -> a) -> f a
defaultTabulate = defaultTabulate' @(LogTypeOf f)
{-# inline defaultTabulate #-}

class DefaultIndexImplC logType f => DefaultIndex' (logType :: LogType) f where
  defaultIndex' :: f a -> Log f -> a

instance DefaultIndexImplC 'UseLogarithm f => DefaultIndex' 'UseLogarithm f where
  defaultIndex' = indexLogarithm
  {-# inline defaultIndex' #-}

instance DefaultIndexImplC 'UseLogRep f => DefaultIndex' 'UseLogRep f where
  defaultIndex' = indexGeneric
  {-# inline defaultIndex' #-}

instance DefaultIndexImplC 'UseLogFin f => DefaultIndex' 'UseLogFin f where
  defaultIndex' = gindexFin
  {-# inline defaultIndex' #-}

type DefaultIndex f = DefaultIndex' (LogTypeOf f) f

defaultIndex :: forall f a. DefaultIndex f => f a -> (Log f -> a)
defaultIndex = defaultIndex' @(LogTypeOf f)
{-# inline defaultIndex #-}

-- | A helper for the most common usage pattern when working with 'scatter'.
--
-- @
-- 'distrib' w k ≡ 'scatter' k id w
-- @
--
-- flipped version of 'cotrav'
distrib :: (Representable f, FFunctor w) => w f -> (w Identity -> r) -> f r
distrib = \ w k -> scatter k id w
{-# inline distrib #-}

-- | The essential essence of the new 'scatter' with administrative mapping removed.
dist :: (Representable f, FFunctor w) => w f -> f (w Identity)
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
  :: (Representable f, FFunctor w)
  => (w Identity -> r)
  -> (g ~> f)
  -> w g -> f r
scatterDefault = \k phi wg ->
  tabulate \x -> k $ ffmap (\g -> Identity $ index (phi g) x) wg
{-# inline scatterDefault #-}

-- | Default definition for 'tabulate' when @'Log' f@ = @'Logarithm' f@. Can be used
-- to manipulate 'Logarithm's regardless of the choice of 'Log' for your distributive
-- functor.
tabulateLogarithm :: Representable f => (Logarithm f -> a) -> f a
tabulateLogarithm = \ f ->
  distrib (Tab f) \(Tab f') -> f' (Logarithm runIdentity)
{-# inline tabulateLogarithm #-}

-- | @'Logarithm' f = f ~> 'Identity'@
--
-- When @f@ is 'Representable', this is the representation/logarithm of @f@, up to isomorphism. i.e.
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
-- This works more generally for any 'Representable' functor. E.g. given
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

-- | A 'Log' for a distributive functor needs to support 'index' and 'tabulate'.
--
-- 'Logarithm' is a universal choice for 'Log'.
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
-- 'distribute' ≡ 'collect' 'id'
-- 'distribute' . 'distribute' ≡ 'id'
-- @
distribute
  :: (Functor f, Representable g)
  => f (g a) -> g (f a)
distribute = \f -> distrib (FCompose f) \(FCompose f') -> runIdentity <$> f'
{-# inline distribute #-}

-- |
-- @
-- 'collect' f ≡ 'distribute' . 'fmap' f
-- 'fmap' f ≡ 'runIdentity' . 'collect' ('Identity' . f)
-- 'fmap' 'distribute' . 'collect' f ≡ 'getCompose' . 'collect' ('Compose' . f)
-- @
collect
  :: (Functor f, Representable g)
  => (a -> g b)
  -> f a -> g (f b)
collect = \ f fa -> distrib (FCompose f) \(FCompose f') -> coerce f' <$> fa
{-# inline collect #-}

-- | The dual of 'Data.Traversable.traverse'
--
-- @
-- 'cotraverse' f ≡ 'fmap' f . 'distribute'
-- @
cotraverse
  :: (Functor f, Representable g)
  => (f a -> b)
  -> f (g a) -> g b
cotraverse = \fab fga ->
  distrib (FCompose fga) \(FCompose f') -> fab (runIdentity <$> f')
{-# inline cotraverse #-}

instance Indexable (Coe a) where
  type Log (Coe a) = a
  index = runCoe
  {-# inline index #-}

instance Representable (Coe a) where
  tabulate = Fun
  {-# inline tabulate #-}
  scatter k f (ffmap f -> w) = Fun \a -> k $ ffmap (\g -> Identity $ runCoe g a) w
  {-# inline scatter #-}

instance (Indexable f, Indexable g) => Indexable (f :*: g) where
  type Log (f :*: g) = Either (Log f) (Log g)
  index = \(f :*: g) -> \case
    Left x -> index f x
    Right y -> index g y
  {-# inline index #-}

instance (Representable f, Representable g) => Representable (f :*: g) where
  scatter = \ k f (ffmap f -> w) ->
        scatter k (\(l :*: _) -> l) w
    :*: scatter k (\(_ :*: r) -> r) w
  tabulate = \ f -> tabulate (f . Left) :*: tabulate (f . Right)
  {-# inline scatter #-}
  {-# inline tabulate #-}

deriving newtype instance Indexable f => Indexable (M1 i c f)
deriving newtype instance Representable f => Representable (M1 i c f)

instance Indexable U1 where
  type Log U1 = Void
  index = \_ -> absurd
  {-# inline index #-}

instance Representable U1 where
  scatter = \_ _ _ -> U1
  tabulate = \_ -> U1
  {-# inline scatter #-}
  {-# inline tabulate #-}

deriving newtype instance Indexable f => Indexable (Rec1 f)
deriving newtype instance Representable f => Representable (Rec1 f)

instance Indexable Par1 where
  type Log Par1 = ()
  index = \x _ -> unPar1 x
  {-# inline index #-}

instance Representable Par1 where
  scatter = \k f -> coerce $ k . ffmap ((Identity . unPar1) #. f)
  tabulate = \f -> Par1 $ f ()
  {-# inline scatter #-}
  {-# inline tabulate #-}

instance (Indexable f, Indexable g) => Indexable (f :.: g) where
  type Log (f :.: g) = (Log f, Log g)
  index = \ (Comp1 f) (x, y) -> index (index f x) y
  {-# inline index #-}

instance (Representable f, Representable g) => Representable (f :.: g) where
  scatter = \ k phi wg ->
    Comp1 $
    scatter
      (scatter k coerce .# runAppDot)
      id
      (AppDot (ffmap phi wg))
  tabulate = \f -> Comp1 $ tabulate \i -> tabulate \j -> f (i, j)
  {-# inline scatter #-}
  {-# inline tabulate #-}

instance (Indexable f, Indexable g) => Indexable (Compose f g) where
  type Log (Compose f g) = Log (Rep1 (Compose f g))
  index (Compose fg) (i,j) = index (index fg i) j
  {-# inline index #-}

instance (Representable f, Representable g) => Representable (Compose f g) where
  tabulate f = Compose $ tabulate \i -> tabulate \j -> f (i,j)
  {-# inline tabulate #-}
  scatter = \ k phi wg ->
    Compose $
    scatter
      (scatter k coerce .# runAppCompose)
      id
      (AppCompose (ffmap phi wg))
  {-# inline scatter #-}

instance (Indexable f, Indexable g) => Indexable (Product f g) where
  type Log (Product f g) = Log (Rep1 (Product f g))
  index = indexGeneric
  {-# inline index #-}

instance (Representable f, Representable g) => Representable (Product f g) where
  tabulate = tabulateGeneric
  {-# inline tabulate #-}

instance Indexable Proxy
instance Representable Proxy

instance Indexable Identity
instance Representable Identity

instance Indexable ((->) x) where
  type Log ((->) x) = x
  index = id
  {-# inline index #-}

instance Representable ((->) x) where
  scatter = \ k phi wg x -> k $ ffmap (\g -> Identity $ phi g x) wg
  tabulate = id
  {-# inline scatter #-}
  {-# inline tabulate #-}

instance Indexable Down
instance Representable Down
instance Indexable Monoid.Product
instance Representable Monoid.Product
instance Indexable Monoid.Sum
instance Representable Monoid.Sum

deriving newtype instance Indexable f => Indexable (Backwards f)
deriving newtype instance Representable f => Representable (Backwards f)
deriving newtype instance Indexable f => Indexable (Reverse f)
deriving newtype instance Representable f => Representable (Reverse f)
deriving newtype instance Indexable f => Indexable (Monoid.Alt f)
deriving newtype instance Representable f => Representable (Monoid.Alt f)
instance Indexable Monoid.Dual
instance Representable Monoid.Dual

deriving newtype instance Indexable f => Indexable (Monoid.Ap f)
deriving newtype instance Representable f => Representable (Monoid.Ap f)

instance Indexable Semigroup.First
instance Representable Semigroup.First
instance Indexable Semigroup.Last
instance Representable Semigroup.Last
instance Indexable Semigroup.Min
instance Representable Semigroup.Min
instance Indexable Semigroup.Max
instance Representable Semigroup.Max

deriving newtype instance (Indexable f, Monad f) => Indexable (WrappedMonad f)
deriving newtype instance (Representable f, Monad f) => Representable (WrappedMonad f)

instance Indexable f => Indexable (Kleisli f a) where
  type Log (Kleisli f a) = (a, Log f)
  index = index .# (Comp1 . runKleisli)
  {-# inline index #-}

instance Representable f => Representable (Kleisli f a) where
  scatter = \k f -> coerce $ scatter k ((Comp1 . runKleisli) #. f)
  tabulate = (Kleisli . unComp1) #. tabulate
  {-# inline scatter #-}
  {-# inline tabulate #-}

#ifdef MIN_VERSION_tagged
instance Indexable (Tagged r)
instance Representable (Tagged r)
#endif

instance Indexable Complex where
  type Log Complex = Bool
  index = \ (r :+ i) -> \case
    False -> r
    True -> i
  {-# inline index #-}

instance Representable Complex where
  tabulate = \ f -> f False :+ f True
  {-# inline tabulate #-}

deriving newtype instance Indexable f => Indexable (IdentityT f)
deriving newtype instance Representable f => Representable (IdentityT f)

deriving via (((->) e :.: f) :: Type -> Type)
  instance Indexable f => Indexable (ReaderT e f)

deriving via (((->) e :.: f) :: Type -> Type)
  instance Representable f => Representable (ReaderT e f)

-- * DerivingVia

-- | Provides defaults definitions for other classes in terms of
-- 'Representable'. Supplied for use with @DerivingVia@ in GHC 8.6+
--
-- Deriving 'Representable', 'Foldable', or 'Traversable' via 'Dist' f leads to non-termination
-- but all other instances are fine for use and are defined in terms of these three.

type role Dist representational nominal
newtype Dist f a = Dist { runDist :: f a }
  deriving stock (Foldable, Traversable)

instance Representable f => Functor (Dist f) where
  fmap = fmapRep
  {-# inline fmap #-}
  (<$) = const . pure
  {-# inline (<$) #-}

-- | A default definition for 'fmap' from 'Functor' in terms of 'Representable'
fmapRep :: Representable f => (a -> b) -> f a -> f b
fmapRep = \ f fa -> distrib (F1 fa) \(F1 a) -> coerce f a
{-# inline fmapRep #-}

instance Indexable f => Indexable (Dist f) where
  type Log (Dist f) = Log f
  index = index .# runDist
  {-# inline index #-}

instance Representable f => Representable (Dist f) where
  scatter = \ k f -> Dist #. scatter k (runDist #. f)
  tabulate = Dist #. tabulate
  {-# inline scatter #-}
  {-# inline tabulate #-}

-- * Applicative

instance Representable f => Applicative (Dist f) where
  pure = pureRep
  {-# inline pure #-}
  (<*>) = apRep
  {-# inline (<*>) #-}
  _ *> m = m
  {-# inline (*>) #-}
  (<*) = const
  {-# inline (<*) #-}
  liftA2 = liftR2
  {-# inline liftA2 #-}

-- | A default definition for 'pure' from 'Applicative' in terms of 'Representable'
pureRep :: Representable f => a -> f a
pureRep = scatter getConst id .# Const
-- pureRep = distrib Proxy . const
{-# inline pureRep #-}

-- | A default definition for '(<*>)' from 'Applicative' in terms of 'Representable'
apRep :: Representable f => f (a -> b) -> f a -> f b
apRep = \fab fa ->
  distrib (F2 fab fa) \(F2 ab a) -> coerce ab a
{-# inline apRep #-}

-- | A default definition 'liftA2' from 'Applicative' in terms of 'Representable'
liftR2 :: Representable f => (a -> b -> c) -> f a -> f b -> f c
liftR2 = \f fa fb ->
  distrib (F2 fa fb) \(F2 a b) -> coerce f a b
{-# inline liftR2 #-}

-- | An implementation of 'liftA3' in terms of 'Representable'.
liftR3 :: Representable f => (a -> b -> c -> d) -> f a -> f b -> f c -> f d
liftR3 = \ f fa fb fc ->
  distrib (F3 fa fb fc) \(F3 a b c) -> coerce f a b c
{-# inline liftR3 #-}

-- | An implementation of 'liftA4' in terms of 'Representable'.
liftR4 :: Representable f => (a -> b -> c -> d -> e) -> f a -> f b -> f c -> f d -> f e
liftR4 = \f fa fb fc fd ->
  distrib (F4 fa fb fc fd) \(F4 a b c d) -> coerce f a b c d
{-# inline liftR4 #-}

-- | An implementation of 'liftA5' in terms of 'Representable'.
liftR5 :: Representable f => (a -> b -> c -> d -> e -> x) -> f a -> f b -> f c -> f d -> f e -> f x
liftR5 = \f fa fb fc fd fe ->
  distrib (F5 fa fb fc fd fe) \(F5 a b c d e) -> coerce f a b c d e
{-# inline liftR5 #-}

-- * Monad

instance Representable f => Monad (Dist f) where
  (>>=) = bindRep
  {-# inline (>>=) #-}
#if !MIN_VERSION_base(4,13,0)
  -- | What are you still doing using 'fail', anyways?
  fail x = tabulate $ \_ -> error x
#endif

-- | A default implementation of '(>>=)' in terms of 'Representable'
bindRep :: Representable f => f a -> (a -> f b) -> f b
bindRep = \ m f -> distrib (F1 m :*: FCompose f) \(F1 a :*: FCompose f') -> coerce f' a
{-# inline bindRep #-}

-- * MonadFix

instance Representable f => MonadFix (Dist f) where
  mfix = mfixRep
  {-# inline mfix #-}

-- | A default definition for 'mfix' in terms of 'Representable'
mfixRep :: Representable f => (a -> f a) -> f a
mfixRep = \ama -> distrib (FCompose ama) (fix . coerce)
{-# inline mfixRep #-}

instance Representable f => MonadZip (Dist f) where
  mzipWith = liftR2
  {-# inline mzipWith #-}
  munzip = fmap fst &&& fmap snd
  {-# inline munzip #-}

instance (Representable f, e ~ Log f) => MonadReader e (Dist f) where
  ask = askRep
  {-# inline ask #-}
  local = localRep
  {-# inline local #-}
  reader = tabulate
  {-# inline reader #-}

instance (Representable f, Num a) => Num (Dist f a) where
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

instance (Representable f, Fractional a) => Fractional (Dist f a) where
  (/) = liftA2 (/)
  recip = fmap recip
  fromRational = pure . fromRational
  {-# inline (/) #-}
  {-# inline recip #-}
  {-# inline fromRational #-}

instance (Representable f, Floating a) => Floating (Dist f a) where
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

instance (Representable f, Semigroup a) => Semigroup (Dist f a) where
  (<>) = liftR2 (<>)
  {-# inline (<>) #-}

instance (Representable f, Monoid a) => Monoid (Dist f a) where
  mempty = pure mempty
  {-# noinline[0] mempty #-}

instance (Representable f, Foldable f, Eq a) => Eq (Dist f a) where
  (==) = eqRep
  {-# inline (==) #-}
  (/=) = neRep
  {-# inline (/=) #-}

eqRep
  :: (Representable f, Foldable f, Eq a)
  => f a -> f a -> Bool
eqRep = \ xs ys ->
  Monoid.getAll $ fold $ liftR2 (\x y -> Monoid.All (x == y)) xs ys
{-# inline eqRep #-}

neRep
  :: (Representable f, Foldable f, Eq a)
  => f a -> f a -> Bool
neRep = \ xs ys ->
  Monoid.getAny $ fold $ liftR2 (\x y -> Monoid.Any (x /= y)) xs ys

instance (Representable f, Foldable f, Ord a) => Ord (Dist f a) where
  compare = \xs ys -> fold $ liftR2 compare xs ys
  {-# inline compare #-}

compareRep
  :: (Representable f, Foldable f, Ord a)
  => f a -> f a -> Ordering
compareRep = \xs ys -> fold $ liftR2 compare xs ys
{-# inline compareRep #-}

liftCompareRep
  :: (Representable f, Foldable f)
  => (a -> b -> Ordering)
  -> f a -> f b -> Ordering
liftCompareRep = \f xs ys -> fold $ liftR2 f xs ys
{-# inline liftCompareRep #-}

liftEqRep :: (Representable f, Foldable f) => (a -> b -> Bool) -> f a -> f b -> Bool
liftEqRep = \f xs ys ->
  Monoid.getAll $ fold $ liftR2 (\x y -> Monoid.All (f x y)) xs ys
{-# inline liftEqRep #-}

instance (Representable f, Foldable f) => Eq1 (Dist f) where
  liftEq = liftEqRep
  {-# inline liftEq #-}

instance (Representable f, Foldable f) => Ord1 (Dist f) where
  liftCompare = liftCompareRep
  {-# inline liftCompare #-}

-- * MonadZip

-- | A default definition for 'mzipWith' in terms of 'Representable'
mzipWithRep :: Representable f => (a -> b -> c) -> f a -> f b -> f c
mzipWithRep = liftR2
{-# inline mzipWithRep #-}

-- * Comonad

#ifdef MIN_VERSION_comonad
instance (Representable f, Monoid (Log f)) => Comonad (Dist f) where
  extract = extractRep
  {-# inline extract #-}
  duplicate = duplicateRep
  {-# inline duplicate #-}
  extend = extendRep
  {-# inline extend #-}

instance (Representable f, Monoid (Log f)) => ComonadApply (Dist f) where
  (<@>) = apRep
  {-# inline (<@>) #-}
  (<@) = const
  {-# inline (<@) #-}
  (@>) = \_ x -> x
  {-# inline (@>) #-}
#endif

-- | A default definition for 'extract' from @Comonad@ in terms of 'Representable'
extractRep :: (Indexable f, Monoid (Log f)) => f a -> a
extractRep = flip index mempty
{-# inline extractRep #-}

-- | A default definition for 'extend' from @Comonad@ in terms of 'Representable'
extendRep :: (Representable f, Semigroup (Log f)) => (f a -> b) -> f a -> f b
extendRep = \f g -> tabulate \i -> f $ tabulate \j -> index g (i <> j)
{-# inline extendRep #-}

-- | A default definition for 'duplicate' from @Comonad@ in terms of 'Representable'
duplicateRep :: (Representable f, Semigroup (Log f)) => f a -> f (f a)
duplicateRep = \f -> tabulate \i -> tabulate \j -> index f (i <> j)
{-# inline duplicateRep #-}

-- | A default definition for 'extract' from @Comonad@ in terms of 'Representable'
-- where the user chooses to supply a 'unit' logarithm other than 'mempty'
extractRepBy :: Indexable f => Log f -> f a -> a
extractRepBy = flip index
{-# inline extractRepBy #-}

-- | A default definition for 'extend' from @Comonad@ in terms of 'Representable'
-- where the user chooses to supply a semigroup on logarithms other than '<>'
extendRepBy :: Representable f => (Log f -> Log f -> Log f) -> (f a -> b) -> f a -> f b
extendRepBy = \t f g -> tabulate \i -> f $ tabulate \j -> index g (t i j)

{-# inline extendRepBy #-}
-- | A default definition for 'duplicate' from @Comonad@ in terms of 'Representable'
-- where the user chooses to supply an semigroup on logarithms other than '<>'
duplicateRepBy :: Representable f => (Log f -> Log f -> Log f) -> f a -> f (f a)
duplicateRepBy = \t f -> tabulate \i -> tabulate \j -> index f (t i j)
{-# inline duplicateRepBy #-}

-- * MonadReader

-- deriving via (f :.: ((->) e)) instance Representable f => Representable (TracedT e f)

-- | A default definition for 'ask' from 'MonadReader' in terms of 'Representable'
askRep :: Representable f => f (Log f)
askRep = tabulate id
{-# noinline[0] askRep #-}

-- | A default definition for 'local' from 'MonadReader' in terms of 'Representable'
localRep :: Representable f => (Log f -> Log f) -> f a -> f a
localRep = \f m -> tabulate (index m . f)
{-# inline localRep #-}

-- * ComonadTrace

-- | A default definition for 'trace' from @ComonadTrace@ in terms of 'Representable'
traceRep :: Indexable f => Log f -> f a -> a
traceRep = flip index
{-# inline traceRep #-}

-- * FunctorWithIndex

instance (Representable f, Log f ~ i) => FunctorWithIndex i (Dist f) where
  imap = imapRep
  {-# inline imap #-}

-- | A default definition for 'imap' from @FunctorWithIndex@ in terms of 'Representable'
imapRep
  :: Representable f
  => (Log f -> a -> b) -> f a -> f b
imapRep = \f xs -> tabulate (f <*> index xs)
{-# inline imapRep #-}

-- * FoldableWithIndex

instance (Representable f, Foldable f, Log f ~ i) => FoldableWithIndex i (Dist f) where
  ifoldMap = ifoldMapRep
  {-# inline ifoldMap #-}

-- | A default definition for 'ifoldMap' from @FoldableWithIndex@ in terms of 'Representable'
ifoldMapRep
  :: forall f m a.
     (Representable f, Foldable f, Monoid m)
  => (Log f -> a -> m) -> f a -> m
ifoldMapRep = \ix xs -> fold (tabulate (\i -> ix i $ index xs i) :: f m)
{-# inline ifoldMapRep #-}

-- * TraversableWithIndex

instance (Representable f, Traversable f, Log f ~ i) => TraversableWithIndex i (Dist f) where
  itraverse = itraverseRep
  {-# inline itraverse #-}

-- | A default definition for 'itraverse' from @TraversableWithIndex@ in terms of 'Representable'
itraverseRep
  :: forall f m a b.
     (Representable f, Traversable f, Applicative m)
  => (Log f -> a -> m b) -> f a -> m (f b)
itraverseRep = \ix xs -> sequenceA $ tabulate (ix <*> index xs)
{-# inline itraverseRep #-}

leftAdjunctRep :: Representable u => ((a, Log u) -> b) -> a -> u b
leftAdjunctRep = \f a -> tabulate (\s -> f (a,s))
{-# inline leftAdjunctRep #-}

rightAdjunctRep :: Indexable u => (a -> u b) -> (a, Log u) -> b
rightAdjunctRep = \f ~(a, k) -> f a `index` k
{-# inline rightAdjunctRep #-}

logarithmPath :: (Representable f, Traversable f) => Logarithm f -> Path
logarithmPath = \ f -> runLogarithm f $ runTrail (traverse id $ pureRep end) id
{-# inline logarithmPath #-}

logPath :: forall f. (Representable f, Traversable f) => Log f -> Path
logPath = index (runTrail (traverse id $ pureRep @f end) id)
{-# inline logPath #-}

#ifdef MIN_VERSION_comonad

instance (Representable f, Comonad f) => Semigroup (Logarithm f) where
  (<>) = \(Logarithm f) (Logarithm g) -> Logarithm \x -> f $ g $ duplicate x
  {-# inline (<>) #-}

instance (Representable f, Comonad f) => Monoid (Logarithm f) where
  mempty = Logarithm extract
  {-# inline mempty #-}

#endif

-- unfortunate orphans, caused by having @hkd@ export the data type
-- rather than making it up here.
instance (Representable f, Traversable f) => Eq (Logarithm f) where
  (==) = on (==) logarithmPath
  {-# inline (==) #-}

instance (Representable f, Traversable f) => Ord (Logarithm f) where
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
eqLog :: forall f. (Representable f, Traversable f) => Log f -> Log f -> Bool
eqLog = on (==) (logPath @f)

-- | Use explicit type application to call this function. e.g. @'neLog' \@f@
--
-- Compare two logarithms for disequality
neLog :: forall f. (Representable f, Traversable f) => Log f -> Log f -> Bool
neLog = on (/=) (logPath @f)

-- | Use explicit type application to call this function. e.g. @'ltLog' \@f@
ltLog :: forall f. (Representable f, Traversable f) => Log f -> Log f -> Bool
ltLog = on (<) (logPath @f)

-- | Use explicit type application to call this function. e.g. @'leLog' \@f@
leLog :: forall f. (Representable f, Traversable f) => Log f -> Log f -> Bool
leLog = on (<=) (logPath @f)

-- | Use explicit type application to call this function. e.g. @'gtLog' \@f@
gtLog :: forall f. (Representable f, Traversable f) => Log f -> Log f -> Bool
gtLog = on (>) (logPath @f)

-- | Use explicit type application to call this function. e.g. @'geLog' \@f@
geLog :: forall f. (Representable f, Traversable f) => Log f -> Log f -> Bool
geLog = on (>=) (logPath @f)

-- | Use explicit type application to call this function. e.g. @'compareLog' \@f@
--
-- Compare two logarithms
compareLog :: forall f. (Representable f, Traversable f) => Log f -> Log f -> Ordering
compareLog = on compare (logPath @f)

-- | For any 'Traversable', each logarithm identifies a 'Lens'.
_logarithm :: Traversable f => Logarithm f -> Lens' (f a) a
_logarithm = \(Logarithm f) a2ga fa ->
  case f $ runTrail (traverse (\a -> (a,) <$> end) fa) id of
    (a, p) -> a2ga a <&> \a' -> runEvil (traverse (\a'' -> Evil a'' (const a')) fa) p
{-# inline _logarithm #-}

-- | We can convert a 'Logarithm' of a 'Representable' functor to any choice of 'Log', as the two forms are canonically isomorphic.
--
-- @
-- 'index' f . 'logFromLogarithm' ≡ 'indexLogarithm' f
-- 'tabulate' (f . 'logFromLogarithm') ≡ 'tabulateLogarithm' f
-- 'logFromLogarithm' '.' 'logToLogarithm' ≡ 'id'
-- 'logToLogarithm' '.' 'logFromLogarithm' ≡ 'id'
-- @
logFromLogarithm :: Representable f => Logarithm f -> Log f
logFromLogarithm = \(Logarithm f) -> f askRep
{-# inline logFromLogarithm #-}

-- | We can convert any 'Log' to a 'Logarithm' as the two types are canonically isomorphic.
--
-- @
-- 'indexLogarithm' f . 'logToLogarithm' ≡ 'index' f
-- 'tabulateLogarithm' (f . 'logToLogarithm') ≡ 'tabulate' f
-- 'logFromLogarithm' '.' 'logToLogarithm' ≡ 'id'
-- 'logToLogarithm' '.' 'logFromLogarithm' ≡ 'id'
-- @
logToLogarithm :: Indexable f => Log f -> Logarithm f
logToLogarithm = \f -> Logarithm (traceRep f)
{-# inline logToLogarithm #-}

-- | For any 'Traversable' 'Representable' each 'Log' determines a 'Lens'.
--
-- @
-- '_log' f = '_logarithm' ('logToLogarithm' f)
-- @
_log :: (Traversable f, Representable f) => Log f -> Lens' (f a) a
_log = \lg a2ga fa ->
  case index (runTrail (traverse (\a -> (a,) <$> end) fa) id) lg of
    (a, p) -> a2ga a <&> \a' -> runEvil (traverse (\a'' -> Evil a'' (const a')) fa) p
{-# inline _log #-}

-- | Construct the lens using @'Eq' ('Log' f)@ instead of with @'Traversable' f@
_logEq :: (Representable f, Eq (Log f)) => Log f -> Lens' (f a) a
_logEq = \i a2ga fa -> a2ga (index fa i) <&> \a' -> imapRep (\j a -> if i == j then a' else a) fa
{-# inline _logEq #-}

type role AppCompose representational nominal nominal
newtype AppCompose w g f = AppCompose { runAppCompose :: w (Compose f g) }

instance FFunctor w => FFunctor (AppCompose w g) where
  ffmap f = AppCompose #. ffmap (Compose #. f .# getCompose) .# runAppCompose
  {-# inline ffmap #-}

-- | By definition representable functors preserve limits.
distributeLim :: Representable f => Lim (Compose f g) -> f (Lim g)
distributeLim xs = distrib (AppCompose xs) \(AppCompose xs') -> ffmap coerce xs'
{-# inline distributeLim #-}

-- | By definition representable functors preserve limits. forall is a limit.
distributeForall :: Representable f => (forall a. f (g a)) -> f (Lim g)
distributeForall xs = distrib (AppCompose (Lim (Compose xs))) \(AppCompose xs') -> ffmap coerce xs'
{-# inline distributeForall #-}

type (%) f g i = f (g i)
infixr 9 %

-- | A higher-kinded 'Logarithm'
--
type role FLogarithm representational nominal
newtype FLogarithm f a = FLogarithm { runFLogarithm :: forall g. f g -> g a }

-- | A higher-kinded 'Tab'
type role FTab representational representational
newtype FTab g f = FTab { runFTab :: FLogarithm f ~> g }

instance FFunctor (FTab g) where
  ffmap f (FTab k) = FTab (\(FLogarithm j) -> k $ FLogarithm (j . f))
  {-# inline ffmap #-}

class FIndexable (f :: (k -> Type) -> Type) where
  -- | A higher-kinded 'Log'
  type FLog f :: k -> Type
  type FLog f = DefaultFLog f

  type KnownIndices f :: Maybe [k]
  type KnownIndices f = DefaultKnownIndices f

  -- | A higher-kinded 'index'
  findex :: f a -> FLog f ~> a
  default findex
     :: (Generic1 f, DefaultFIndex f)
     => f a -> FLog f ~> a
  findex = defaultFIndex @(GFInvalid (Rep1 f))
  {-# inline findex #-}

class (FIndexable f, FFunctor f) => FRepresentable (f :: (k -> Type) -> Type) where

  -- | A higher-kinded 'scatter'
  fscatter :: FFunctor w => (w % F1 ~> r) -> (g ~> f) -> w g -> f r
  default fscatter
    :: (Generic1 f, FRepresentable (Rep1 f), FFunctor w)
    => (w % F1 ~> r) -> (g ~> f) -> w g -> f r
  fscatter = fscatterGeneric
  {-# inline fscatter #-}

  -- | A higher-kinded 'tabulate'
  ftabulate :: (FLog f ~> a) -> f a
  default ftabulate
    :: (Generic1 f, DefaultFTabulate f)
    => (FLog f ~> a) -> f a
  ftabulate = defaultFTabulate @(GFInvalid (Rep1 f))
  {-# inline ftabulate #-}

-- | A higher-kinded 'distrib'
fdistrib
  :: (FFunctor w, FRepresentable f)
  => w f -> (w % F1 ~> r) -> f r
fdistrib = \ w k -> fscatter k id w
{-# inline fdistrib #-}

-- | A higher-kinded 'tabulateLogarithm'
ftabulateFLogarithm
  :: FRepresentable f => (FLogarithm f ~> a) -> f a
ftabulateFLogarithm
  = \f -> fdistrib (FTab f) \(FTab f') -> f' (FLogarithm runF1)
{-# inline ftabulateFLogarithm #-}

-- | A higher-kinded 'indexLogarithm'
findexFLogarithm :: f a -> FLogarithm f ~> a
findexFLogarithm = \fa (FLogarithm k) -> k fa
{-# inline findexFLogarithm #-}

-- | A higher-kinded 'tabulateGeneric'
ftabulateGeneric
  :: forall f a.
     (FRepresentable (Rep1 f), Generic1 f, Coercible (FLog f) (FLog (Rep1 f)))
  => (FLog f ~> a) -> f a
ftabulateGeneric = \f -> to1 $ ftabulate (\x -> f (coerce x))
{-# inline ftabulateGeneric #-}

-- | A higher-kinded 'indexGeneric'
findexGeneric
  :: forall f a.
     (FIndexable (Rep1 f), Generic1 f, Coercible (FLog f) (FLog (Rep1 f)))
  => f a -> FLog f ~> a
findexGeneric = \fa flog -> findex (from1 fa) (coerce flog)
{-# inline findexGeneric #-}

-- | A higher-kinded 'scatterGeneric'
fscatterGeneric
  :: (FRepresentable (Rep1 f), Generic1 f, FFunctor w)
  => (w % F1 ~> r) -> (g ~> f) -> w g -> f r
fscatterGeneric = \k phi -> to1 . fscatter k (from1 . phi)
{-# inline fscatterGeneric #-}

fscatterDefault
  :: (FRepresentable f, FFunctor w)
  => (w % F1 ~> r)
  -> (g ~> f)
  -> w g -> f r
fscatterDefault = \k phi wg ->
  ftabulate \x -> k $ ffmap (\g -> F1 $ findex (phi g) x) wg
{-# inline fscatterDefault #-}

-- | A higher-kinded 'Tabulate'
pattern FTabulate :: FRepresentable f => (FLog f ~> a) -> f a
pattern FTabulate i <- (findex -> i) where
  FTabulate i = ftabulate i

type family DefaultFLog' (containsRec1 :: Bool) (f :: (i -> Type) -> Type) :: i -> Type where
  DefaultFLog' 'True  f = FLogarithm f
  DefaultFLog' 'False f = FLog (Rep1 f)

type family DefaultFImplC (containsRec1 :: Bool) f :: Constraint where
  DefaultFImplC 'True  f = (FRepresentable f, FLog f ~ FLogarithm f)
  DefaultFImplC 'False f = (Generic1 f, FRepresentable (Rep1 f), Coercible (FLog f) (FLog (Rep1 f)))

-- individual type classes, so there is GHC needs to less work
class DefaultFImplC containsRec1 f => DefaultFTabulate' (containsRec1 :: Bool) f where
  defaultFTabulate :: (FLog f ~> a) -> f a

instance DefaultFImplC 'True f => DefaultFTabulate' 'True f where
  defaultFTabulate = ftabulateFLogarithm
  {-# inline defaultFTabulate #-}

instance DefaultFImplC 'False f => DefaultFTabulate' 'False f where
  defaultFTabulate = ftabulateGeneric
  {-# inline defaultFTabulate #-}

class DefaultFImplC containsRec1 f => DefaultFIndex' (containsRec1 :: Bool) f where
  defaultFIndex :: f a -> FLog f ~> a

instance DefaultFImplC 'True f => DefaultFIndex' 'True f where
  defaultFIndex = findexFLogarithm
  {-# inline defaultFIndex #-}

instance DefaultFImplC 'False f => DefaultFIndex' 'False f where
  defaultFIndex = findexGeneric
  {-# inline defaultFIndex #-}

type DefaultFLog f = DefaultFLog' (GFInvalid (Rep1 f)) f
type DefaultFTabulate f = DefaultFTabulate' (GFInvalid (Rep1 f)) f
type DefaultFIndex f = DefaultFIndex' (GFInvalid (Rep1 f)) f

-- | A higher-kinded 'distribute'
--
-- @
-- 'fdistribute' = 'fcollect' 'id'
-- @
fdistribute
  :: (Functor f, FRepresentable g)
  => f (g a) -> g (Compose f a)
fdistribute = \f ->
  fdistrib (FCompose f) \(FCompose f') ->
    Compose $ fmap coerce f'
{-# inline fdistribute #-}

-- | A higher-kinded 'collect'
--
-- @
-- 'fcollect' f = 'fdistribute' . 'fmap' f
-- @
fcollect
  :: (Functor f, FRepresentable g)
  => (a -> g b)
  -> f a -> g (Compose f b)
fcollect = \f fa ->
  fdistrib (FCompose f) \(FCompose f') ->
    Compose $ fmap (coerce f') fa
{-# inline fcollect #-}

-- | A higher-kinded 'cotraverse'
--
-- @
-- 'fcotraverse' f = 'fmap' f . 'fdistribute'
-- @
fcotraverse
  :: (Functor f, FRepresentable g)
  => (f % a ~> b)
  -> f (g a) -> g b
fcotraverse = \fab fga ->
  fdistrib (FCompose fga) \(FCompose f') ->
    fab (fmap coerce f')
{-# inline fcotraverse #-}

instance (FIndexable f, FIndexable g) => FIndexable (f :*: g) where
  type FLog (f :*: g) = FLog f :+: FLog g
  findex = \(f :*: g) -> \case
    L1 x -> findex f x
    R1 y -> findex g y
  {-# inline findex #-}

instance (FRepresentable f, FRepresentable g) => FRepresentable (f :*: g) where
  fscatter = \k f (ffmap f -> w) ->
        fscatter k (\(l :*: _) -> l) w
    :*: fscatter k (\(_ :*: r) -> r) w
  ftabulate = \f -> ftabulate (f . L1) :*: ftabulate (f . R1)
  {-# inline fscatter #-}
  {-# inline ftabulate #-}

deriving newtype instance FIndexable f => FIndexable (M1 i c f)
deriving newtype instance FRepresentable f => FRepresentable (M1 i c f)

instance FIndexable U1 where
  type FLog U1 = V1
  findex = \_ -> \case
  {-# inline findex #-}

instance FRepresentable U1 where
  fscatter = \_ _ _ -> U1
  ftabulate = \_ -> U1
  {-# inline fscatter #-}
  {-# inline ftabulate #-}

deriving newtype instance FIndexable f => FIndexable (Rec1 f)
deriving newtype instance FRepresentable f => FRepresentable (Rec1 f)

instance (Indexable f, FIndexable g) => FIndexable (f :.: g) where
  type FLog (f :.: g) = K1 R (Log f) :*: FLog g
  findex = \(Comp1 f) (K1 x :*: y) -> findex (index f x) y
  {-# inline findex #-}

instance (Representable f, FRepresentable g) => FRepresentable (f :.: g) where
  fscatter = \k phi wg -> Comp1 $
    scatter (fscatter k coerce .# runAppDot) id $ AppDot (ffmap phi wg)
  ftabulate = \f -> Comp1 $ tabulate \i -> ftabulate \j -> f (K1 i :*: j)
  {-# inline fscatter #-}
  {-# inline ftabulate #-}

instance (Indexable f, FIndexable g) => FIndexable (Compose f g) where
  type FLog (Compose f g) = K1 R (Log f) :*: FLog g
  findex = \(Compose f) (K1 x :*: y) -> findex (index f x) y
  {-# inline findex #-}

instance (Representable f, FRepresentable g) => FRepresentable (Compose f g) where
  ftabulate = \f -> Compose $ tabulate \i -> ftabulate \j -> f (K1 i :*: j)
  {-# inline ftabulate #-}
  fscatter = \k phi wg -> Compose $
    scatter (fscatter k coerce .# runAppCompose) id $ AppCompose (ffmap phi wg)
  {-# inline fscatter #-}

instance (FIndexable f, FIndexable g) => FIndexable (Product f g) where
  type FLog (Product f g) = FLog (Rep1 (Product f g))
  findex = findexGeneric
  {-# inline findex #-}

instance (FRepresentable f, FRepresentable g) => FRepresentable (Product f g) where
  ftabulate = ftabulateGeneric
  {-# inline ftabulate #-}

instance FIndexable Proxy
instance FRepresentable Proxy

deriving newtype instance FIndexable f => FIndexable (Backwards f)
deriving newtype instance FIndexable f => FIndexable (Reverse f)
deriving newtype instance FIndexable f => FIndexable (Monoid.Alt f)
deriving newtype instance FIndexable f => FIndexable (Monoid.Ap f)

deriving newtype instance FRepresentable f => FRepresentable (Backwards f)
deriving newtype instance FRepresentable f => FRepresentable (Reverse f)
deriving newtype instance FRepresentable f => FRepresentable (Monoid.Alt f)
deriving newtype instance FRepresentable f => FRepresentable (Monoid.Ap f)

instance FIndexable (F1 a) where
  type FLog (F1 a) = (:~:) a
  findex = \f Refl -> runF1 f
  {-# inline findex #-}

instance FRepresentable (F1 a) where
  fscatter = \k f w -> F1 $ k $ ffmap f w
  ftabulate = \f -> F1 (f Refl)
  {-# inline fscatter #-}
  {-# inline ftabulate #-}

instance FIndexable (NT f) where
  type FLog (NT f) = f
  findex = runNT
  {-# inline findex #-}

instance FRepresentable (NT f) where
  fscatter = fscatterDefault
  ftabulate = NT
  {-# inline ftabulate #-}
  {-# inline fscatter #-}

instance FIndexable Lim where
  type FLog Lim = U1
  findex f = const $ runLim f
  {-# inline findex #-}

instance FRepresentable Lim where
  fscatter = \k f w -> Lim $ k $ ffmap (\x -> F1 $ runLim $ f x) w
  ftabulate = \f -> Lim $ f U1
  {-# inline ftabulate #-}
  {-# inline fscatter #-}

-- TODO: FLog (F2 a b) = Index '[a,b], etc.

instance FIndexable (F2 a b) where
  type FLog (F2 a b) = FLogarithm (F2 a b)
  findex = findexFLogarithm
  {-# inline findex #-}

instance FRepresentable (F2 a b) where
  ftabulate = ftabulateFLogarithm
  fscatter = \k f (ffmap f -> w) ->
     F2 (k $ ffmap (\(F2 x _) -> F1 x) w)
        (k $ ffmap (\(F2 _ y) -> F1 y) w)
  {-# inline ftabulate #-}
  {-# inline fscatter #-}

instance FIndexable (F3 a b c) where
  type FLog (F3 a b c) = FLogarithm (F3 a b c)
  findex = findexFLogarithm
  {-# inline findex #-}

instance FRepresentable (F3 a b c) where
  ftabulate = ftabulateFLogarithm
  fscatter = \k f (ffmap f -> w) ->
     F3 (k $ ffmap (\(F3 x _ _) -> F1 x) w)
        (k $ ffmap (\(F3 _ x _) -> F1 x) w)
        (k $ ffmap (\(F3 _ _ x) -> F1 x) w)
  {-# inline ftabulate #-}
  {-# inline fscatter #-}

instance FIndexable (F4 a b c d) where
  type FLog (F4 a b c d) = FLogarithm (F4 a b c d)
  findex = findexFLogarithm
  {-# inline findex #-}

instance FRepresentable (F4 a b c d) where
  ftabulate = ftabulateFLogarithm
  fscatter = \k f (ffmap f -> w) ->
     F4 (k $ ffmap (\(F4 x _ _ _) -> F1 x) w)
        (k $ ffmap (\(F4 _ x _ _) -> F1 x) w)
        (k $ ffmap (\(F4 _ _ x _) -> F1 x) w)
        (k $ ffmap (\(F4 _ _ _ x) -> F1 x) w)
  {-# inline ftabulate #-}
  {-# inline fscatter #-}

instance FIndexable (F5 a b c d e) where
  type FLog (F5 a b c d e) = FLogarithm (F5 a b c d e)
  findex = findexFLogarithm
  {-# inline findex #-}

instance FRepresentable (F5 a b c d e) where
  ftabulate = ftabulateFLogarithm
  fscatter = \k f (ffmap f -> w) ->
     F5 (k $ ffmap (\(F5 x _ _ _ _) -> F1 x) w)
        (k $ ffmap (\(F5 _ x _ _ _) -> F1 x) w)
        (k $ ffmap (\(F5 _ _ x _ _) -> F1 x) w)
        (k $ ffmap (\(F5 _ _ _ x _) -> F1 x) w)
        (k $ ffmap (\(F5 _ _ _ _ x) -> F1 x) w)
  {-# inline ftabulate #-}
  {-# inline fscatter #-}

-- | A higher-kinded 'Dist'
type role FDist representational nominal
newtype FDist f a = FDist { runFDist :: f a }
  deriving stock (Data, Generic, Generic1)
  deriving newtype (FFoldable)

instance (FRepresentable f, FTraversable f) => FTraversable (FDist f) where
  ftraverse = \f -> fmap FDist . ftraverse f .# runFDist
  {-# inline ftraverse #-}

deriving newtype instance FIndexable f => FIndexable (FDist f)
deriving newtype instance FRepresentable f => FRepresentable (FDist f)

-- | A default definition for 'ffmap' from 'FFunctor' in terms of 'FRepresentable'
ffmapRep :: FRepresentable f => (a ~> b) -> f a -> f b
ffmapRep = \f -> fscatter (f .# (runF1 . runF1)) id .# F1
{-# inline ffmapRep #-}

instance FRepresentable f => FFunctor (FDist f) where
  ffmap = ffmapRep
  {-# inline ffmap #-}

instance FRepresentable f => FApply (FDist f) where
  fliftA2 = fliftR2
  {-# inline fliftA2 #-}

fliftR2 :: FRepresentable f => (forall x. a x -> b x -> c x) -> f a -> f b -> f c
fliftR2 = \f m n ->
  fdistrib (F2 m n) \(F2 (F1 m') (F1 n')) -> f m' n'
{-# inline fliftR2 #-}

fliftR3 :: FRepresentable f => (forall x. a x -> b x -> c x -> d x) -> f a -> f b -> f c -> f d
fliftR3 = \f m n o ->
  fdistrib (F3 m n o) \(F3 (F1 m') (F1 n') (F1 o')) -> f m' n' o'
{-# inline fliftR3 #-}

fliftR4 :: FRepresentable f => (forall x. a x -> b x -> c x -> d x -> e x) -> f a -> f b -> f c -> f d -> f e
fliftR4 = \f m n o p ->
  fdistrib (F4 m n o p) \(F4 (F1 m') (F1 n') (F1 o') (F1 p')) -> f m' n' o' p'
{-# inline fliftR4 #-}

fliftR5 :: FRepresentable f => (forall x. a x -> b x -> c x -> d x -> e x -> r x) -> f a -> f b -> f c -> f d -> f e -> f r
fliftR5 = \f m n o p q ->
  fdistrib (F5 m n o p q) \(F5 (F1 m') (F1 n') (F1 o') (F1 p') (F1 q')) -> f m' n' o' p' q'
{-# inline fliftR5 #-}

instance FRepresentable f => FApplicative (FDist f) where
  fpure = fpureRep
  {-# inline fpure #-}

-- | A default definition of 'fpure' from 'FApplicative' in terms of 'FRepresentable'
fpureRep :: FRepresentable f => (forall x. a x) -> f a
fpureRep = \ax -> fscatter (\x -> runLim (getConst x)) id $ Const $ Lim ax
-- fpureRep a = fdistrib Proxy \_ -> a
{-# inline fpureRep #-}

instance FFunctor (DFBind a b) where
  ffmap = \f (DFBind fa afb) -> DFBind (f fa) (f . afb)
  {-# inline ffmap #-}

data DFBind a b f = DFBind (f a) (a ~> f % b)

fbindRep :: FRepresentable f => f a -> (a ~> f % Coatkey b) -> f b
fbindRep = \fa f -> fdistrib (DFBind fa f) \(DFBind (F1 a) ab) -> runCoatkey $ runF1 (ab a)
{-# inline fbindRep #-}

instance FRepresentable f => FBind (FDist f) where
  fbind = \(FDist fa) f -> FDist $ fbindRep fa (runFDist #. f)
  {-# inline fbind #-}

faskRep :: FRepresentable f => f (FLog f)
faskRep = ftabulate id
{-# noinline[0] faskRep #-}

ftraceRep :: FIndexable f => FLog f a -> f g -> g a
ftraceRep = \x y -> findex y x

-- | We can convert a 'FLogarithm' of a 'FRepresentable' 'FFunctor' to any choice
-- of 'FLog', as the two forms are canonically isomorphic.
--
-- @
-- 'findex' f . 'flogFromLogarithm' ≡ 'findexLogarithm' f
-- 'ftabulate' (f . 'flogFromLogarithm') ≡ 'ftabulateLogarithm' f
-- 'flogFromLogarithm' '.' 'flogToLogarithm' ≡ 'id'
-- 'flogToLogarithm' '.' 'flogFromLogarithm' ≡ 'id'
-- @
flogFromFLogarithm :: FRepresentable f => FLogarithm f ~> FLog f
flogFromFLogarithm = \(FLogarithm f) -> f faskRep
{-# inline flogFromFLogarithm #-}

-- | We can convert any 'FLog' to a 'FLogarithm' as the two types are canonically isomorphic.
--
-- @
-- 'findexLogarithm' f . 'flogToLogarithm' ≡ 'findex' f
-- 'ftabulateLogarithm' (f . 'flogToLogarithm') ≡ 'ftabulate' f
-- 'flogFromLogarithm' '.' 'flogToLogarithm' ≡ 'id'
-- 'flogToLogarithm' '.' 'flogFromLogarithm' ≡ 'id'
-- @
flogToFLogarithm :: FIndexable f => FLog f ~> FLogarithm f
flogToFLogarithm = \f -> FLogarithm (ftraceRep f)
{-# inline flogToFLogarithm #-}

-- if HKD took x as its first parameter i could use FCompose
type role DHKD representational nominal nominal
newtype DHKD w x f = DHKD { runDHKD :: w (HKD f x) }
instance FFunctor w => FFunctor (DHKD w x) where
  ffmap f = DHKD #. ffmap (mapHKD f) .# runDHKD
  {-# inline ffmap #-}

instance Indexable f => FIndexable (HKD f x) where
  type FLog (HKD f x) = Atkey (Log f) x
  findex = \(HKD fa) (Atkey lg) -> runF1 (index fa lg)
  {-# inline findex #-}

instance Representable f => FRepresentable (HKD f x) where
  fscatter = \k g (ffmap g -> w) -> HKD $ distrib (DHKD w) $ F1 #. k . ffmap coerce .# runDHKD
  {-# inline fscatter #-}
  ftabulate = \f -> HKD $ tabulate (F1 #. f . Atkey)
  {-# inline ftabulate #-}

-------------------------------------------------------------------------------
-- HKD
-------------------------------------------------------------------------------

lowerLogarithm :: FLogarithm f x -> Logarithm (LKD f)
lowerLogarithm = \(FLogarithm f) -> Logarithm $ getConst #. f .# runLKD
{-# inline lowerLogarithm #-}

liftLogarithm :: FRepresentable f => Logarithm (LKD f) -> Some (FLogarithm f)
liftLogarithm = \(Logarithm f) -> f $ LKD $ ftabulateFLogarithm (Const #. Some)
{-# inline liftLogarithm #-}

instance FIndexable f => Indexable (LKD f) where
  type Log (LKD f) = Some (FLog f)
  index = \fa (Some lg) -> getConst (findex (runLKD fa) lg)
  {-# inline index #-}

type role DLKD representational nominal
newtype DLKD w f = DLKD { runDLKD :: w (LKD f) }

instance FFunctor w => FFunctor (DLKD w) where
  ffmap = \f -> DLKD #. ffmap (LKD #. f .# runLKD) .# runDLKD
  {-# inline ffmap #-}

instance FRepresentable f => Representable (LKD f) where
  scatter = \k g -> LKD . fscatter (Const #. k .  ffmap coerce .# runDLKD) id . DLKD . ffmap g
  {-# inline scatter #-}
  tabulate = \f -> LKD $ ftabulate (Const #. f . Some)
  {-# inline tabulate #-}


instance (FTraversable f, FRepresentable f) => Eq (FLogarithm f a) where
  (==) = on (==) lowerLogarithm
  {-# inline (==) #-}

instance (FTraversable f, FRepresentable f) => Ord (FLogarithm f a) where
  compare = on compare lowerLogarithm
  {-# inline compare #-}

-- safer than it looks
instance (FTraversable f, FRepresentable f) => GEq (FLogarithm f) where
  geq = \x y ->
    if lowerLogarithm x == lowerLogarithm y
    then Just (unsafeCoerce Refl)
    else Nothing
  {-# inline geq #-}

geqFLog :: forall f a b. (FRepresentable f, FTraversable f) => FLog f a -> FLog f b -> Maybe (a :~: b)
geqFLog x y = geq (flogFPath @f x) (flogFPath @f y)
{-# inline geqFLog #-}

gcompareFLog :: forall f a b. (FRepresentable f, FTraversable f) => FLog f a -> FLog f b -> GOrdering a b
gcompareFLog x y = gcompare (flogFPath @f x) (flogFPath @f y)
{-# inline gcompareFLog #-}

instance (FTraversable f, FRepresentable f) => TestEquality (FLogarithm f) where
  testEquality = geq
  {-# inline testEquality #-}

instance (FTraversable f, FRepresentable f) => TestCoercion (FLogarithm f) where
  testCoercion = \x y -> repr <$> geq x y
  {-# inline testCoercion #-}

instance (FTraversable f, FRepresentable f) => GCompare (FLogarithm f) where
  gcompare = \x y -> case compare (lowerLogarithm x) (lowerLogarithm y) of
    LT -> GLT
    EQ -> unsafeCoerce GEQ
    GT -> GGT
  {-# inline gcompare #-}

flogFPath :: forall f. (FRepresentable f, FTraversable f) => FLog f ~> FPath Proxy
flogFPath = findex $ runTrail (ftraverse fend $ fpureRep @f Proxy) id
{-# inline flogFPath #-}

type Lens' s a = forall f. Functor f => (a -> f a) -> s -> f s

type role FPath representational nominal
data FPath f a = FPath (f a) Path

instance GEq (FPath f) where
  geq = \(FPath _ x) (FPath _ y) ->
    if x == y
    then Just (unsafeCoerce Refl)
    else Nothing
  {-# inline geq #-}

instance GCompare (FPath f) where
  gcompare = \(FPath _ x) (FPath _ y) -> case compare x y of
    LT -> GLT
    EQ -> unsafeCoerce GEQ
    GT -> GGT
  {-# inline gcompare #-}

fend :: f a -> Trail (FPath f a)
fend a = FPath a <$> end

_flogarithm :: FTraversable t => FLogarithm t a -> Lens' (t f) (f a)
_flogarithm = \(FLogarithm f) a2ga tf ->
  case f $ runTrail (ftraverse fend tf) id of
    FPath a p -> a2ga a <&> \a' -> runEvil (ftraverse (\a'' -> Evil a'' (const (unsafeCoerce a'))) tf) p
{-# inline _flogarithm #-}

_flog :: (FTraversable t, FRepresentable t) => FLog t a -> Lens' (t f) (f a)
_flog = \i a2ga tf ->
  case findex (runTrail (ftraverse fend tf) id) i of
    FPath a p -> a2ga a <&> \a' -> runEvil (ftraverse (\a'' -> Evil a'' (const (unsafeCoerce a'))) tf) p
{-# inline _flog #-}

-- | Construct the lens for a logarithm using @'GEq' ('FLog' t)@ instead of with @'FTraversable' t@
_flogGEq :: (FRepresentable t, GEq (FLog t)) => FLog t a -> Lens' (t f) (f a)
_flogGEq = \i a2ga fa -> a2ga (findex fa i) <&> \a' -> ifmapRep (\j a -> case geq i j of
  Just Refl -> a'
  Nothing -> a) fa
{-# inline _flogGEq #-}

instance (FRepresentable f, FLog f ~ i) => FFunctorWithIndex i (FDist f) where
  ifmap = ifmapRep
  {-# inline ifmap #-}

ifmapRep
  :: forall f a b. FRepresentable f
  => (forall x. FLog f x -> a x -> b x) -> f a -> f b
ifmapRep = \f -> fliftR2 f is
  where is = faskRep :: f (FLog f)
{-# inline ifmapRep #-}

instance (FRepresentable f, FFoldable f, FLog f ~ i) => FFoldableWithIndex i (FDist f) where
  iffoldMap = iffoldMapRep
  {-# inline iffoldMap #-}

-- | A default definition for 'ifoldMap' from @FoldableWithIndex@ in terms of 'Representable'
iffoldMapRep
  :: forall f m a.
     (FRepresentable f, FFoldable f, Monoid m)
  => (forall x. FLog f x -> a x -> m) -> f a -> m
iffoldMapRep = \f -> ffoldMap getConst . ifmapRep (\i -> Const #. f i)
{-# inline iffoldMapRep #-}

instance (FRepresentable f, FTraversable f, FLog f ~ i) => FTraversableWithIndex i (FDist f) where
  iftraverse = iftraverseRep
  {-# inline iftraverse #-}

iftraverseRep
  :: forall f m a b.
     (FRepresentable f, FTraversable f, Applicative m)
  => (forall x. FLog f x -> a x -> m (b x)) -> f a -> m (f b)
iftraverseRep = \f -> ftraverse getCompose . ifmapRep (\i -> Compose #. f i)
{-# inline iftraverseRep #-}

instance FIndexable (FConstrained p) where
  type FLog (FConstrained p) = Dict1 p
  findex = \(FConstrained x) Dict1 -> x

instance FRepresentable (FConstrained p) where
  fscatter = \k f (ffmap f -> w) -> FConstrained $ k $ ffmap (\(FConstrained x) -> F1 x) w
  ftabulate = \f -> FConstrained $ f Dict1

class FAll (p :: i -> Constraint) (f :: (i -> Type) -> Type) where
  fall :: f (Dict1 p)
  default fall :: (Generic1 f, FAll p (Rep1 f)) => f (Dict1 p)
  fall = to1 fall

instance (FAll p f, FAll p g) => FAll p (f :*: g) where
  fall = fall :*: fall

instance (Representable f, FAll p g) => FAll p (f :.: g) where
  fall = Comp1 $ pureRep fall

deriving newtype instance FAll p f => FAll p (M1 i c f)
deriving newtype instance FAll p f => FAll p (Rec1 f)

instance FAll p U1 where fall = U1

instance FAll p Proxy

instance a ~ Dict1 p => FAll p ((:~:) a) where
  fall = Refl

instance p a => FAll p (F1 a) where
  fall = F1 Dict1

instance (p a, p b) => FAll p (F2 a b) where
  fall = F2 Dict1 Dict1

instance (p a, p b, p c) => FAll p (F3 a b c) where
  fall = F3 Dict1 Dict1 Dict1

instance (p a, p b, p c, p d) => FAll p (F4 a b c d) where
  fall = F4 Dict1 Dict1 Dict1 Dict1

instance (p a, p b, p c, p d, p e) => FAll p (F5 a b c d e) where
  fall = F5 Dict1 Dict1 Dict1 Dict1 Dict1

instance q (Dict1 p) => FAll p (Dict1 q) where
  fall = Dict1

instance (Representable f, FAll p g) => FAll p (Compose f g)

instance (FAll p f, FAll p g) => FAll p (Product f g)

-- this is arguably any existential constraint
instance (forall a. p a) => FAll p Some where fall = Some Dict1
instance (forall a. p a) => FAll p Lim where fall = Lim Dict1
instance (forall a. q a => p a) => FAll p (FConstrained q) where
  fall = FConstrained Dict1

fliftA2W :: (FRepresentable f, FFunctor w) => (forall x. a x -> w (F1 x) -> r x) -> f a -> w f -> f r
fliftA2W f fa w = fdistrib (F1 fa :*: w) \(F1 (F1 a) :*: w') -> f a w'

cfdistrib
  :: forall i (p :: i -> Constraint) (f :: (i -> Type) -> Type) (r :: i -> Type) w.
     (FAll p f, FFunctor w, FRepresentable f)
  => w f
  -> (forall x. p x => w (F1 x) -> r x)
  -> f r
cfdistrib w k = fliftA2W (\Dict1 -> k) (fall @i @p) w

{-
type family EqC :: k -> Constraint where
  EqC = Eq
  EqC = FEq

class DefaultFEq (w :: k -> Type) where
  feqDefault :: EqC i => w i -> w i -> Bool

instance (Representable w, Foldable w) => DefaultFEq (w :: Type -> Type) where
  feqDefault = \x -> and . liftR2 (==) x

instance (FRepresentable w, FFoldable w, FAll EqC w) => DefaultFEq (w :: (k -> Type) -> Type) where
  feqDefault = \x y ->
    Monoid.getAll $
    ffoldMap getConst $
    fliftR3
      (\(Dict1 :: Dict1 EqC x) (i :: f x) (j :: f x) -> Const $ Monoid.All $ feq i j)
      (fall @_ @EqC)
      x
      y

class (forall i. EqC i => Eq (w i)) => FEq w
instance (forall i. EqC i => Eq (w i)) => FEq w

feq :: (FEq w, EqC i) => w i -> w i -> Bool
feq = (==)

-- type FEq w = forall i. EqC i => Eq (w i) :: Constraint

{-
class FEq (w :: k -> Type) where
  feq :: EqC i => w i -> w i -> Bool
  default feq :: (DefaultFEq w, EqC i) => w i -> w i -> Bool
  feq = feqDefault
  {-# inline feq #-}
-}

instance Eq (F0 x)
instance (EqC a, EqC b, DefaultFEq f) => Eq (F2 a b f) where
  (==) = feqDefault
{-
--instance FEq V1 where feq = (==)
--instance FEq U1 where feq _ _ = True
--instance FEq F0 where feq _ _ = True
instance FEq Proxy where feq _ _ = True

instance Eq a => FEq (Const a) where feq = (==)
instance Eq a => FEq (Constant a) where feq = (==)
instance EqC a => FEq (F1 a)
instance (EqC a, EqC b) => FEq (F2 a b)
instance (EqC a, EqC b, EqC c) => FEq (F3 a b c)
instance (EqC a, EqC b, EqC c, EqC d) => FEq (F4 a b c d)
instance (EqC a, EqC b, EqC c, EqC d, EqC e) => FEq (F5 a b c d e)

instance (FEq f, FEq g) => FEq (f :*: g) where
  feq (a :*: b) (a' :*: b') = feq a a' && feq b b'

instance (FEq f, FEq g) => FEq (f :+: g) where
  feq (L1 a) (L1 a') = feq a a'
  feq (R1 b) (R1 b') = feq b b'
  feq _ _ = False

instance (Eq1 f, FEq g) => FEq (f :.: g) where
  feq (Comp1 x) (Comp1 y) = liftEq feq x y
-}
-}

-- * Internals

-- Does @(Rep1 f)@ contain @'Rec1' f@, @K1@, @V1@, sums or a @Par1@?
-- In any of these cases 'tabulateGeneric/indexGeneric and defining
-- @Log f = Log (Rep1 f)@ will fail. In all of these cases
-- we'll default to using Logarithm.
-- In the other case we could try to use 'Index' or
type family GInvalid' (f :: j -> Type) (parValid :: Bool) (i :: Nat) :: Bool where
  GInvalid' _          _ 0 = 'True
  GInvalid' (K1 _ _)   _ i = 'True
  GInvalid' (M1 _ _ f) p i = GInvalid' f p i
  GInvalid' U1         _ i = 'False
  GInvalid' V1         _ i = 'True -- not
  GInvalid' Par1       p _ = p
  GInvalid' (f :*: g)  p i = GInvalid' f p i || GInvalid' g p i
  GInvalid' (f :+: g)  _ i = 'True
  GInvalid' (f :.: g)  p i = GInvalid' (Rep1 f) 'True i || GInvalid' g p i
  -- this clause is a hack. If pieces @f@ is built from are not 'Generic1',
  -- this will get stuck.
  --
  -- An alternative with non-linear match is suboptimal in other ways
  GInvalid' (Rec1 f)   p i = GInvalid' (Rep1 f) p (i - 1)

-- Log (Rep1 f) is usable
type GInvalid (f :: j -> Type) = GInvalid' f 'False SearchDepth

-- FLog (Rep1 f) is usable
type GFInvalid (f :: j -> Type) = GInvalid' f 'True SearchDepth

type family IsJust (xs :: Maybe a) :: Bool where
  IsJust ('Just x) = 'True
  IsJust 'Nothing = 'False

type family IsNothing (xs :: Maybe a) :: Bool where
  IsNothing ('Just x) = 'False
  IsNothing 'Nothing = 'True

type family FromJust (xs :: Maybe a) :: a where
  FromJust ('Just x) = x

-- assumes we're not GInvalid
type family GUnknownSize (f :: j -> Type) :: Bool where
  GUnknownSize (M1 _ _ f) = GUnknownSize f
  GUnknownSize U1 = 'False
  GUnknownSize Par1 = 'False
  GUnknownSize (f :*: g) = GUnknownSize f || GUnknownSize g
  GUnknownSize (f :.: g) = IsNothing (KnownSize f) || GUnknownSize g
  GUnknownSize (Rec1 f) = IsNothing (KnownSize f)

-- assumes we're not GInvalid and don't have GUnknownSize
type family GSize (f :: j -> Type) :: Nat where
  GSize (M1 _ _ f) = GSize f
  GSize U1 = 0
  GSize Par1 = 1
  GSize (f :*: g) = GSize f + GSize g
  GSize (f :.: g) = Size f * GSize g
  GSize (Rec1 f) = Size f

type family (++) (f :: [i]) (g :: [i]) :: [i] where
  '[] ++ ys = ys
  (x ': xs) ++ ys = x ': (xs ++ ys)

type family Repeat (n :: Nat) (as :: [i]) :: [i] where
  Repeat 0 as = '[]
  Repeat n as = as ++ Repeat (n - 1) as

type family GUnknownIndices (f :: j -> Type) :: Bool where
  GUnknownIndices (M1 _ _ f) = GUnknownIndices f
  GUnknownIndices U1 = 'False
  GUnknownIndices (f :*: g) = GUnknownIndices f || GUnknownIndices g
  GUnknownIndices (f :.: g) = IsNothing (KnownSize f) || GUnknownIndices g
  GUnknownIndices (Rec1 f) = IsNothing (KnownIndices f)

type family GIndices' (f :: (k -> Type) -> Type) (acc :: [k]) :: [k] where
  GIndices' (M1 _ _ f) as = GIndices' f as
  GIndices' U1 as = as
  GIndices' (f :*: g) as = GIndices' f (GIndices' g as)
  GIndices' (f :.: g) as = Repeat (Size f) (GIndices g) ++ as
  GIndices' (Rec1 f) as = Indices f ++ as

type GIndices (f :: (k -> Type) -> Type) = GIndices' f '[]

type GKnownSize (f :: j -> Type) =
  If (GInvalid f || GUnknownSize f)
     'Nothing
     ('Just (GSize f))

type GKnownIndices (f :: (j -> Type) -> Type) =
  If (GFInvalid f || GUnknownIndices f)
     'Nothing
    ('Just (GIndices f))

type DefaultKnownSize f = GKnownSize (Rep1 f)
type DefaultKnownIndices f = GKnownIndices (Rep1 f)

type SearchDepth = 3

type role AppDot representational nominal nominal
newtype AppDot w g f = AppDot { runAppDot :: w (f :.: g) }
instance FFunctor w => FFunctor (AppDot w g) where
  ffmap f = AppDot #. ffmap (Comp1 #. f .# unComp1) .# runAppDot
  {-# inline ffmap #-}


data Path = End | L Path | R Path deriving (Eq, Ord, Show, Read)

-- This is not a legal 'Applicative', but it is used towards legal ends.

type role Trail representational
newtype Trail a = Trail { runTrail :: (Path -> Path) -> a }
  deriving Functor

instance Applicative Trail where
  pure = Trail . const
  {-# inline pure #-}

  (<*>) = \fab fa -> Trail \k -> runTrail fab (k . L) $ runTrail fa (k . R)
  {-# inline (<*>) #-}

end :: Trail Path
end = Trail \k -> k End
{-# inline end #-}

-- This is also not a legal 'Applicative', but it is used towards legal ends.

type role Evil representational
data Evil a = Evil a (Path -> a)
  deriving Functor

instance Applicative Evil where
  pure = \a -> Evil a \_ -> a
  {-# inline pure #-}
  (<*>) = \ ~(Evil mb mg) ~(Evil nb ng) -> Evil (mb nb) \case
    L xs -> mg xs nb
    R xs -> mb (ng xs)
    End -> undefined
  {-# inline (<*>) #-}

runEvil :: Evil a -> Path -> a
runEvil = \(Evil _ mg) -> mg
{-# inline runEvil #-}

-- for testing
data V2 a = V2 a a
  deriving stock (Show, Read, Functor, Foldable, Traversable, Generic, Generic1, Data)
  deriving anyclass (Indexable, Representable)
  deriving (Eq1,Ord1,Applicative, Monad, MonadFix, MonadZip) via Dist V2
  deriving (Eq,Ord,Num,Fractional,Floating,Semigroup,Monoid) via Dist V2 a

instance Show1 V2 where
  liftShowsPrec f _ d (V2 a b) = showParen (d > 10) $ showString "V2 " . f 11 a . showChar ' ' . f 11 b

class
  ( Traversable f
  , Representable f
  , IsJust (KnownSize f) ~ 'True
  , KnownNat (Size f)
  ) => FiniteRepresentable f

instance
  ( Traversable f
  , Representable f
  , IsJust (KnownSize f) ~ 'True
  , KnownNat (Size f)
  ) => FiniteRepresentable f

type Size f = FromJust (KnownSize f)
type Indices f = FromJust (KnownIndices f)

type LogFin f = Fin (Size f)
type FLogIndex f = Index (Indices f)

type HasLogFin f = Log f == LogFin f

lie :: a
lie = error "Data.Functor.Rep.Internal: logic error. index out of bounds or invalid Size f"

class DefaultIndexFin' (b :: Bool) (f :: Type -> Type) where
  indexFinDefault :: f a -> LogFin f -> a

instance (Log f ~ LogFin f, Representable f) => DefaultIndexFin' 'True f where
  indexFinDefault = index
  {-# inline indexFinDefault #-}

type f /~ g = (f == g) ~ 'False

instance (Log f /~ LogFin f, FiniteRepresentable f) => DefaultIndexFin' 'False f where
  indexFinDefault = \ f (Fin i) ->
    fromMaybe lie $
    Monoid.getFirst $
    fold $
    liftR2
      (\(Fin j) a -> Monoid.First $ if i == j then Just a else Nothing)
      askFin
      f
  {-# inline indexFinDefault #-}

type DefaultIndexFin f = DefaultIndexFin' (HasLogFin f) f

indexFin :: forall f a. DefaultIndexFin f => f a -> LogFin f -> a
indexFin = indexFinDefault @(HasLogFin f)
{-# inline indexFin #-}

-- assumes GSize f is defined and can be KnownNat
class GIndexFin f where
  gunsafeIndexFin :: f a -> LogFin f -> a

deriving newtype instance GIndexFin f => GIndexFin (M1 i c f)

-- this would be better if it knew if f has an index that was Fin (Size f) and used index instead
instance DefaultIndexFin f => GIndexFin (Rec1 f) where
  gunsafeIndexFin (Rec1 fa) (Fin i) = indexFin fa (UnsafeFin i)
  {-# inline gunsafeIndexFin #-}

instance GIndexFin U1 where
  gunsafeIndexFin U1 (Fin _) = lie

instance GIndexFin Par1 where
  gunsafeIndexFin (Par1 x) (Fin 0) = x
  gunsafeIndexFin _ _ = lie
  {-# inline gunsafeIndexFin #-}

instance (KnownNat (GSize f), GIndexFin f, GIndexFin g) => GIndexFin (f :*: g) where
  gunsafeIndexFin (f :*: g) (Fin i)
    | i < j = gunsafeIndexFin f (UnsafeFin i)
    | otherwise = gunsafeIndexFin g (UnsafeFin $ i - j)
    where j = int @(GSize f)
  {-# inline gunsafeIndexFin #-}

instance (DefaultIndexFin f, KnownNat (GSize g), GIndexFin g) => GIndexFin (f :.: g) where
  gunsafeIndexFin (Comp1 fg) (Fin i) = case quotRem i $ int @(GSize g) of
    (q, r) -> gunsafeIndexFin (indexFin fg (UnsafeFin q)) (UnsafeFin r)
  {-# inline gunsafeIndexFin #-}

gindexFin :: (Generic1 f, GIndexFin (Rep1 f), Log f ~ LogFin f, Size f ~ GSize (Rep1 f)) => f a -> LogFin f -> a
gindexFin fa (Fin i) = gunsafeIndexFin (from1 fa) (UnsafeFin i)
{-# inline gindexFin #-}

askFin :: DefaultTabulateFin f => f (LogFin f)
askFin = tabulateFin id
{-# inline[0] askFin #-}

class GTabulateFin f where
  gunsafeTabulateFin :: (Fin (GSize f) -> a) -> f a

instance GTabulateFin U1 where
  gunsafeTabulateFin _ = U1

instance DefaultTabulateFin f => GTabulateFin (Rec1 f) where
  gunsafeTabulateFin f = Rec1 $ tabulateFin f
  {-# inline gunsafeTabulateFin #-}

deriving newtype instance GTabulateFin f => GTabulateFin (M1 i c f)

instance GTabulateFin Par1 where
  gunsafeTabulateFin f = Par1 $ f (UnsafeFin 0)
  {-# inline gunsafeTabulateFin #-}

instance (KnownNat (GSize f), GTabulateFin f, GTabulateFin g) => GTabulateFin (f :*: g) where
  gunsafeTabulateFin f =
        gunsafeTabulateFin (coerce f)
    :*: gunsafeTabulateFin (\(Fin i) -> f (UnsafeFin (i + j)))
    where j = int @(GSize f)
  {-# inline gunsafeTabulateFin #-}

instance (DefaultTabulateFin f, KnownNat (GSize g), GTabulateFin g) => GTabulateFin (f :.: g) where
  gunsafeTabulateFin f =
    Comp1 $
    tabulateFin \(Fin i) ->
    gunsafeTabulateFin \(Fin j) ->
    f $ UnsafeFin (i * k + j)
    where k = int @(GSize g)
  {-# inline gunsafeTabulateFin #-}

class DefaultTabulateFin' (b :: Bool) (f :: Type -> Type) where
  tabulateFinDefault :: (LogFin f -> a) -> f a

instance (Log f ~ LogFin f, Representable f) => DefaultTabulateFin' 'True f where
  tabulateFinDefault = tabulate
  {-# inline tabulateFinDefault #-}

instance (Log f /~ LogFin f, FiniteRepresentable f) => DefaultTabulateFin' 'False f where
  tabulateFinDefault f =
    case mapAccumL (\n () -> (n + 1, f $ UnsafeFin n)) 0 (pureRep ()) of
    (n', xs)
      | n' == int @(Size f) -> xs
      | otherwise -> lie
  {-# inline tabulateFinDefault #-}

type DefaultTabulateFin f = DefaultTabulateFin' (HasLogFin f) f

tabulateFin :: forall f a. DefaultTabulateFin f => (LogFin f -> a) -> f a
tabulateFin = tabulateFinDefault @(HasLogFin f)
{-# inline tabulateFin #-}

gtabulateFin
  :: (Generic1 f, GTabulateFin (Rep1 f))
  => (Fin (GSize (Rep1 f)) -> a) -> f a
gtabulateFin f = to1 $ gunsafeTabulateFin f
{-# inline gtabulateFin #-}

#ifdef MIN_VERSION_comonad
instance Indexable w => Indexable (TracedT m w) where
  type Log (TracedT m w) = (Log w, m)
  index (TracedT wma) (lw,m) = index wma lw m

instance Representable w => Representable (TracedT m w) where

instance Indexable w => Indexable (Cokleisli w a) where
  type Log (Cokleisli w a) = w a
  index (Cokleisli f) w = f w
  {-# inline index #-}

instance Representable w => Representable (Cokleisli w a) where
  tabulate = Cokleisli
  {-# inline tabulate #-}
#endif
