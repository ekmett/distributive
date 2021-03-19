{-# Language CPP #-}
{-# Language GeneralizedNewtypeDeriving #-}
{-# Language Unsafe #-}
{-# options_haddock not-home #-}

-- |
-- Copyright   : (C) 2011-2021 Edward Kmett,
--               (c) 2017-2021 Aaron Vargo,
--               (c) 2021 Oleg Grenrus
-- License     : BSD-style (see the file LICENSE)
-- Maintainer  : Edward Kmett <ekmett@gmail.com>
-- Stability   : provisional
-- Portability : non-portable (ghc 8.6+)

module Data.Distributive.Internal where

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
import Data.Distributive.Internal.Coerce
import Data.Distributive.Internal.Fin
import Data.Distributive.Internal.Orphans ()
import Data.Foldable (fold)
import Data.Foldable.WithIndex
import Data.Function
import Data.Functor
import Data.Functor.Classes
import Data.Functor.Compose
import Data.Functor.Contravariant
import Data.Functor.Contravariant.Divisible
import Data.Functor.Identity
import Data.Functor.Product
import Data.Functor.Reverse
import Data.Functor.WithIndex
import Data.GADT.Compare
import Data.HKD
import Data.HKD.Contravariant
import Data.HKD.Internal.Index
import Data.HKD.WithIndex
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

class Indexable f where
  -- | Defaults to @'Log' ('Rep1' f)@ when @f@ is non-recursive, otherwise to 'Logarithm'.
  type Log f
  type Log f = DefaultLog f

  type KnownSize f :: Maybe Nat
  type KnownSize f = DefaultKnownSize f

  -- | Defaults to 'indexLogarithm' when @'Log' f = 'Logarithm' f@, otherwise to 'indexRep'
  index :: f a -> Log f -> a
  default index :: DefaultIndex f => f a -> Log f -> a
  index = defaultIndex
  {-# inline index #-}

class (Indexable f, Functor f) => Distributive f where

  -- | Defaults to 'tabulateLogarithm' when @'Log' f = 'Logarithm' f@, otherwise to 'tabulateRep'
  tabulate :: (Log f -> a) -> f a
  default tabulate :: DefaultTabulate f => (Log f -> a) -> f a
  tabulate = defaultTabulate
  {-# inline tabulate #-}

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
  -- 'scatter' phi wg ≡ 'tabulate' \\x -> 'ffmap' (\\g -> 'Identity' '$' 'index' (phi g) x) wg
  -- @
  --
  -- Defaults to 'scatterRep'
  --
  -- The obvious API for this function is the much simpler
  --
  -- @
  -- 'dist ':: ('Distributive' f, 'FFunctor' w) => w f -> f (w 'Identity')
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
  -- 'distrib' :: ('Distributive' f, 'FFunctor' w) => w f -> (w 'Identity' -> r) -> f r
  -- @
  --
  -- as well, outside o the class, which is quite concise for many workloads.
  scatter :: FFunctor w => (w Identity -> r) -> (g ~> f) -> w g -> f r
  default scatter
    :: (Generic1 f, Distributive (Rep1 f), FFunctor w)
    => (w Identity -> r) -> (g ~> f) -> w g -> f r
  scatter = scatterRep
  {-# inline scatter #-}

-- | derive tabulate via 'Generic1' when @'Log' f@ is (a possible newtype of)
-- @'Log' ('Rep1' f)@
tabulateRep
  :: forall f a.
     (Distributive (Rep1 f), Generic1 f, Coercible (Log f) (Log (Rep1 f)))
  => (Log f -> a) -> f a
tabulateRep = coerce (to1 . tabulate :: (Log (Rep1 f) -> a) -> f a)
{-# inline tabulateRep #-}

-- | derive 'index' via 'Generic1' when @'Log' f@ is (a possible newtype of)
-- @'Log' ('Rep1' f)@
indexRep
  :: forall f a.
     (Indexable (Rep1 f), Generic1 f, Coercible (Log f) (Log (Rep1 f)))
  => f a -> Log f -> a
indexRep = coerce (index . from1 :: f a -> Log (Rep1 f) -> a)
{-# inline indexRep #-}

-- | derive 'scatter' via 'Generic1'
scatterRep
  :: (Distributive (Rep1 f), Generic1 f, FFunctor w)
  => (w Identity -> r) -> (g ~> f) -> w g -> f r
scatterRep = \k phi -> to1 . scatter k (from1 . phi)
{-# inline scatterRep #-}

-- | This pattern synonym lets you work with any 'Distributive' functor as if
-- it were a function.
pattern Tabulate :: Distributive f => (Log f -> a) -> f a
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
  DefaultTabulateImplC 'UseLogarithm f = (Distributive f, Log f ~ Logarithm f)
  DefaultTabulateImplC 'UseLogRep f = (Generic1 f, Distributive (Rep1 f), Coercible (Log f) (Log (Rep1 f)))
  DefaultTabulateImplC 'UseLogFin f = (Generic1 f, GTabulateFin (Rep1 f), Size f ~ GSize (Rep1 f), Log f ~ Fin (GSize (Rep1 f)))

type family DefaultIndexImplC (t :: LogType) f :: Constraint where
  DefaultIndexImplC 'UseLogarithm f = (Log f ~ Logarithm f)
  DefaultIndexImplC 'UseLogRep f = (Generic1 f, Distributive (Rep1 f), Coercible (Log f) (Log (Rep1 f)))
  DefaultIndexImplC 'UseLogFin f = (Generic1 f, GIndexFin (Rep1 f), Size f ~ GSize (Rep1 f), Log f ~ Fin (GSize (Rep1 f)))

-- individual type classes, so GHC needs to do less work
class DefaultTabulateImplC logType f => DefaultTabulate' (logType :: LogType) f where
  defaultTabulate' :: (Log f -> a) -> f a

instance DefaultTabulateImplC 'UseLogarithm f => DefaultTabulate' 'UseLogarithm f where
  defaultTabulate' = tabulateLogarithm
  {-# inline defaultTabulate' #-}

instance DefaultTabulateImplC 'UseLogRep f => DefaultTabulate' 'UseLogRep f where
  defaultTabulate' = tabulateRep
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
  defaultIndex' = indexRep
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
  tabulate \x -> k $ ffmap (\g -> Identity $ index (phi g) x) wg
{-# inline scatterDefault #-}

-- | Default definition for 'tabulate' when @'Log' f@ = @'Logarithm' f@. Can be used
-- to manipulate 'Logarithm's regardless of the choice of 'Log' for your distributive
-- functor.
tabulateLogarithm :: Distributive f => (Logarithm f -> a) -> f a
tabulateLogarithm = \ f ->
  distrib (Tab f) \(Tab f') -> f' (Logarithm runIdentity)
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
  :: (Functor f, Distributive g)
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
  :: (Functor f, Distributive g)
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
  :: (Functor f, Distributive g)
  => (f a -> b)
  -> f (g a) -> g b
cotraverse = \fab fga ->
  distrib (FCompose fga) \(FCompose f') -> fab (runIdentity <$> f')
{-# inline cotraverse #-}

instance (Indexable f, Indexable g) => Indexable (f :*: g) where
  type Log (f :*: g) = Either (Log f) (Log g)
  index = \(f :*: g) -> \case
    Left x -> index f x
    Right y -> index g y
  {-# inline index #-}

instance (Distributive f, Distributive g) => Distributive (f :*: g) where
  scatter = \ k f (ffmap f -> w) ->
        scatter k (\(l :*: _) -> l) w
    :*: scatter k (\(_ :*: r) -> r) w
  tabulate = \ f -> tabulate (f . Left) :*: tabulate (f . Right)
  {-# inline scatter #-}
  {-# inline tabulate #-}


deriving newtype instance Indexable f => Indexable (M1 i c f)
deriving newtype instance Distributive f => Distributive (M1 i c f)

instance Indexable U1 where
  type Log U1 = Void
  index = \_ -> absurd
  {-# inline index #-}

instance Distributive U1 where
  scatter = \_ _ _ -> U1
  tabulate = \_ -> U1
  {-# inline scatter #-}
  {-# inline tabulate #-}

deriving newtype instance Indexable f => Indexable (Rec1 f)
deriving newtype instance Distributive f => Distributive (Rec1 f)

instance Indexable Par1 where
  type Log Par1 = ()
  index = \x _ -> unPar1 x
  {-# inline index #-}

instance Distributive Par1 where
  scatter = \k f -> coerce $ k . ffmap ((Identity . unPar1) #. f)
  tabulate = \f -> Par1 $ f ()
  {-# inline scatter #-}
  {-# inline tabulate #-}

instance (Indexable f, Indexable g) => Indexable (f :.: g) where
  type Log (f :.: g) = (Log f, Log g)
  index = \ (Comp1 f) (x, y) -> index (index f x) y
  {-# inline index #-}

instance (Distributive f, Distributive g) => Distributive (f :.: g) where
  scatter = \ k phi wg ->
    Comp1 $
    scatter
      (scatter k coerce .# runAppCompose)
      id
      (AppCompose (ffmap phi wg))
  tabulate = \f -> Comp1 $ tabulate \i -> tabulate \j -> f (i, j)
  {-# inline scatter #-}
  {-# inline tabulate #-}

-- TODO: Why Functor f?
instance (Functor f, Indexable f, Indexable g) => Indexable (Compose f g) where
  type Log (Compose f g) = Log (Rep1 (Compose f g))
  index = indexRep
  {-# inline index #-}

instance (Distributive f, Distributive g) => Distributive (Compose f g) where
  tabulate = tabulateRep
  {-# inline tabulate #-}

instance (Indexable f, Indexable g) => Indexable (Product f g) where
  type Log (Product f g) = Log (Rep1 (Product f g))
  index = indexRep
  {-# inline index #-}

instance (Distributive f, Distributive g) => Distributive (Product f g) where
  tabulate = tabulateRep
  {-# inline tabulate #-}

instance Indexable Proxy
instance Distributive Proxy

instance Indexable Identity
instance Distributive Identity

instance Indexable ((->) x) where
  type Log ((->) x) = x
  index = id
  {-# inline index #-}

instance Distributive ((->) x) where
  scatter = \ k phi wg x -> k $ ffmap (\g -> Identity $ phi g x) wg
  tabulate = id
  {-# inline scatter #-}
  {-# inline tabulate #-}

instance Indexable Down
instance Distributive Down
instance Indexable Monoid.Product
instance Distributive Monoid.Product
instance Indexable Monoid.Sum
instance Distributive Monoid.Sum

deriving newtype instance Indexable f => Indexable (Backwards f)
deriving newtype instance Distributive f => Distributive (Backwards f)
deriving newtype instance Indexable f => Indexable (Reverse f)
deriving newtype instance Distributive f => Distributive (Reverse f)
deriving newtype instance Indexable f => Indexable (Monoid.Alt f)
deriving newtype instance Distributive f => Distributive (Monoid.Alt f)
instance Indexable Monoid.Dual
instance Distributive Monoid.Dual

deriving newtype instance Indexable f => Indexable (Monoid.Ap f)
deriving newtype instance Distributive f => Distributive (Monoid.Ap f)

instance Indexable Semigroup.First
instance Distributive Semigroup.First
instance Indexable Semigroup.Last
instance Distributive Semigroup.Last
instance Indexable Semigroup.Min
instance Distributive Semigroup.Min
instance Indexable Semigroup.Max
instance Distributive Semigroup.Max

deriving newtype instance (Indexable f, Monad f) => Indexable (WrappedMonad f)
deriving newtype instance (Distributive f, Monad f) => Distributive (WrappedMonad f)

instance Indexable f => Indexable (Kleisli f a) where
  type Log (Kleisli f a) = (a, Log f)
  index = index .# (Comp1 . runKleisli)
  {-# inline index #-}

instance Distributive f => Distributive (Kleisli f a) where
  scatter = \k f -> coerce $ scatter k ((Comp1 . runKleisli) #. f)
  tabulate = (Kleisli . unComp1) #. tabulate
  {-# inline scatter #-}
  {-# inline tabulate #-}

-- instance Distributive f => Distributive (Cokleisli f a)

#ifdef MIN_VERSION_tagged
instance Indexable (Tagged r)
instance Distributive (Tagged r)
#endif

instance Indexable Complex where
  type Log Complex = Bool
  index = \ (r :+ i) -> \case
    False -> r
    True -> i
  {-# inline index #-}

instance Distributive Complex where
  tabulate = \ f -> f False :+ f True
  {-# inline tabulate #-}

deriving newtype instance Indexable f => Indexable (IdentityT f)
deriving newtype instance Distributive f => Distributive (IdentityT f)

deriving via (((->) e :.: f) :: Type -> Type)
  instance Indexable f => Indexable (ReaderT e f)

deriving via (((->) e :.: f) :: Type -> Type)
  instance Distributive f => Distributive (ReaderT e f)

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
fmapDist = \ f fa -> distrib (F1 fa) \(F1 a) -> coerce f a
{-# inline fmapDist #-}

instance Indexable f => Indexable (Dist f) where
  type Log (Dist f) = Log f
  index = index .# runDist
  {-# inline index #-}

instance Distributive f => Distributive (Dist f) where
  scatter = \ k f -> Dist #. scatter k (runDist #. f)
  tabulate = Dist #. tabulate
  {-# inline scatter #-}
  {-# inline tabulate #-}

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
  distrib (F2 fab fa) \(F2 ab a) -> coerce ab a
{-# inline apDist #-}

-- | A default definition 'liftA2' from 'Applicative' in terms of 'Distributive'
liftD2 :: Distributive f => (a -> b -> c) -> f a -> f b -> f c
liftD2 = \f fa fb ->
  distrib (F2 fa fb) \(F2 a b) -> coerce f a b
{-# inline liftD2 #-}

-- | An implementation of 'liftA3' in terms of 'Distributive'.
liftD3 :: Distributive f => (a -> b -> c -> d) -> f a -> f b -> f c -> f d
liftD3 = \ f fa fb fc ->
  distrib (F3 fa fb fc) \(F3 a b c) -> coerce f a b c
{-# inline liftD3 #-}

-- | An implementation of 'liftA4' in terms of 'Distributive'.
liftD4 :: Distributive f => (a -> b -> c -> d -> e) -> f a -> f b -> f c -> f d -> f e
liftD4 = \f fa fb fc fd ->
  distrib (F4 fa fb fc fd) \(F4 a b c d) -> coerce f a b c d
{-# inline liftD4 #-}

-- | An implementation of 'liftA5' in terms of 'Distributive'.
liftD5 :: Distributive f => (a -> b -> c -> d -> e -> x) -> f a -> f b -> f c -> f d -> f e -> f x
liftD5 = \f fa fb fc fd fe ->
  distrib (F5 fa fb fc fd fe) \(F5 a b c d e) -> coerce f a b c d e
{-# inline liftD5 #-}

-- * Monad

instance Distributive f => Monad (Dist f) where
  (>>=) = bindDist
  {-# inline (>>=) #-}

-- | A default implementation of '(>>=)' in terms of 'Distributive'
bindDist :: Distributive f => f a -> (a -> f b) -> f b
bindDist = \ m f -> distrib (F1 m :*: FCompose f) \(F1 a :*: FCompose f') -> coerce f' a
{-# inline bindDist #-}

-- * MonadFix

instance Distributive f => MonadFix (Dist f) where
  mfix = mfixDist
  {-# inline mfix #-}

-- | A default definition for 'mfix' in terms of 'Distributive'
mfixDist :: Distributive f => (a -> f a) -> f a
mfixDist = \ama -> distrib (FCompose ama) (fix . coerce)
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
extractDist :: (Indexable f, Monoid (Log f)) => f a -> a
extractDist = flip index mempty
{-# inline extractDist #-}

-- | A default definition for 'extend' from @Comonad@ in terms of 'Distributive'
extendDist :: (Distributive f, Semigroup (Log f)) => (f a -> b) -> f a -> f b
extendDist = \f g -> tabulate \i -> f $ tabulate \j -> index g (i <> j)
{-# inline extendDist #-}

-- | A default definition for 'duplicate' from @Comonad@ in terms of 'Distributive'
duplicateDist :: (Distributive f, Semigroup (Log f)) => f a -> f (f a)
duplicateDist = \f -> tabulate \i -> tabulate \j -> index f (i <> j)
{-# inline duplicateDist #-}

-- | A default definition for 'extract' from @Comonad@ in terms of 'Distributive'
-- where the user chooses to supply a 'unit' logarithm other than 'mempty'
extractDistBy :: Indexable f => Log f -> f a -> a
extractDistBy = flip index
{-# inline extractDistBy #-}

-- | A default definition for 'extend' from @Comonad@ in terms of 'Distributive'
-- where the user chooses to supply a semigroup on logarithms other than '<>'
extendDistBy :: Distributive f => (Log f -> Log f -> Log f) -> (f a -> b) -> f a -> f b
extendDistBy = \t f g -> tabulate \i -> f $ tabulate \j -> index g (t i j)

{-# inline extendDistBy #-}
-- | A default definition for 'duplicate' from @Comonad@ in terms of 'Distributive'
-- where the user chooses to supply an semigroup on logarithms other than '<>'
duplicateDistBy :: Distributive f => (Log f -> Log f -> Log f) -> f a -> f (f a)
duplicateDistBy = \t f -> tabulate \i -> tabulate \j -> index f (t i j)
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
traceDist :: Indexable f => Log f -> f a -> a
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

rightAdjunctDist :: Indexable u => (a -> u b) -> (a, Log u) -> b
rightAdjunctDist = \f ~(a, k) -> f a `index` k
{-# inline rightAdjunctDist #-}

logarithmPath :: (Distributive f, Traversable f) => Logarithm f -> Path
logarithmPath = \ f -> runLogarithm f $ runTrail (traverse id $ pureDist end) id
{-# inline logarithmPath #-}

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
logToLogarithm :: Indexable f => Log f -> Logarithm f
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

class (FIndexable f, FFunctor f) => FDistributive (f :: (k -> Type) -> Type) where

  -- | A higher-kinded 'scatter'
  fscatter :: FFunctor w => (w % F1 ~> r) -> (g ~> f) -> w g -> f r
  default fscatter
    :: (Generic1 f, FDistributive (Rep1 f), FFunctor w)
    => (w % F1 ~> r) -> (g ~> f) -> w g -> f r
  fscatter = fscatterRep
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
  :: (FFunctor w, FDistributive f)
  => w f -> (w % F1 ~> r) -> f r
fdistrib = \ w k -> fscatter k id w
{-# inline fdistrib #-}

-- | A higher-kinded 'tabulateLogarithm'
ftabulateFLogarithm
  :: FDistributive f => (FLogarithm f ~> a) -> f a
ftabulateFLogarithm
  = \f -> fdistrib (FTab f) \(FTab f') -> f' (FLogarithm runF1)
{-# inline ftabulateFLogarithm #-}

-- | A higher-kinded 'indexLogarithm'
findexFLogarithm :: f a -> FLogarithm f ~> a
findexFLogarithm = \fa (FLogarithm k) -> k fa
{-# inline findexFLogarithm #-}

-- | A higher-kinded 'tabulateRep'
ftabulateRep
  :: forall f a.
     (FDistributive (Rep1 f), Generic1 f, Coercible (FLog f) (FLog (Rep1 f)))
  => (FLog f ~> a) -> f a
ftabulateRep = \f -> to1 $ ftabulate (\x -> f (coerce x))
{-# inline ftabulateRep #-}

-- | A higher-kinded 'indexRep'
findexRep
  :: forall f a.
     (FIndexable (Rep1 f), Generic1 f, Coercible (FLog f) (FLog (Rep1 f)))
  => f a -> FLog f ~> a
findexRep = \fa flog -> findex (from1 fa) (coerce flog)
{-# inline findexRep #-}

-- | A higher-kinded 'scatterRep'
fscatterRep
  :: (FDistributive (Rep1 f), Generic1 f, FFunctor w)
  => (w % F1 ~> r) -> (g ~> f) -> w g -> f r
fscatterRep = \k phi -> to1 . fscatter k (from1 . phi)
{-# inline fscatterRep #-}

fscatterDefault
  :: (FDistributive f, FFunctor w)
  => (w % F1 ~> r)
  -> (g ~> f)
  -> w g -> f r
fscatterDefault = \k phi wg ->
  ftabulate \x -> k $ ffmap (\g -> F1 $ findex (phi g) x) wg
{-# inline fscatterDefault #-}

-- | A higher-kinded 'Tabulate'
pattern FTabulate :: FDistributive f => (FLog f ~> a) -> f a
pattern FTabulate i <- (findex -> i) where
  FTabulate i = ftabulate i

type family DefaultFLog' (containsRec1 :: Bool) (f :: (i -> Type) -> Type) :: i -> Type where
  DefaultFLog' 'True  f = FLogarithm f
  DefaultFLog' 'False f = FLog (Rep1 f)

type family DefaultFImplC (containsRec1 :: Bool) f :: Constraint where
  DefaultFImplC 'True  f = (FDistributive f, FLog f ~ FLogarithm f)
  DefaultFImplC 'False f = (Generic1 f, FDistributive (Rep1 f), Coercible (FLog f) (FLog (Rep1 f)))

-- individual type classes, so there is GHC needs to less work
class DefaultFImplC containsRec1 f => DefaultFTabulate' (containsRec1 :: Bool) f where
  defaultFTabulate :: (FLog f ~> a) -> f a

instance DefaultFImplC 'True f => DefaultFTabulate' 'True f where
  defaultFTabulate = ftabulateFLogarithm
  {-# inline defaultFTabulate #-}

instance DefaultFImplC 'False f => DefaultFTabulate' 'False f where
  defaultFTabulate = ftabulateRep
  {-# inline defaultFTabulate #-}

class DefaultFImplC containsRec1 f => DefaultFIndex' (containsRec1 :: Bool) f where
  defaultFIndex :: f a -> FLog f ~> a

instance DefaultFImplC 'True f => DefaultFIndex' 'True f where
  defaultFIndex = findexFLogarithm
  {-# inline defaultFIndex #-}

instance DefaultFImplC 'False f => DefaultFIndex' 'False f where
  defaultFIndex = findexRep
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
  :: (Functor f, FDistributive g)
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
  :: (Functor f, FDistributive g)
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
  :: (Functor f, FDistributive g)
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

instance (FDistributive f, FDistributive g) => FDistributive (f :*: g) where
  fscatter = \k f (ffmap f -> w) ->
        fscatter k (\(l :*: _) -> l) w
    :*: fscatter k (\(_ :*: r) -> r) w
  ftabulate = \f -> ftabulate (f . L1) :*: ftabulate (f . R1)
  {-# inline fscatter #-}
  {-# inline ftabulate #-}

deriving newtype instance FIndexable f => FIndexable (M1 i c f)
deriving newtype instance FDistributive f => FDistributive (M1 i c f)

instance FIndexable U1 where
  type FLog U1 = V1
  findex = \_ -> \case
  {-# inline findex #-}

instance FDistributive U1 where
  fscatter = \_ _ _ -> U1
  ftabulate = \_ -> U1
  {-# inline fscatter #-}
  {-# inline ftabulate #-}

deriving newtype instance FIndexable f => FIndexable (Rec1 f)
deriving newtype instance FDistributive f => FDistributive (Rec1 f)

instance (Indexable f, FIndexable g) => FIndexable (f :.: g) where
  type FLog (f :.: g) = K1 R (Log f) :*: FLog g
  findex = \(Comp1 f) (K1 x :*: y) -> findex (index f x) y
  {-# inline findex #-}

instance (Distributive f, FDistributive g) => FDistributive (f :.: g) where
  fscatter = \k phi wg -> Comp1 $
    scatter (fscatter k coerce .# runAppCompose) id $ AppCompose (ffmap phi wg)
  ftabulate = \f -> Comp1 $ tabulate \i -> ftabulate \j -> f (K1 i :*: j)
  {-# inline fscatter #-}
  {-# inline ftabulate #-}

-- TODO: why Functor f?
instance (Functor f, Indexable f, FIndexable g) => FIndexable (Compose f g) where
  type FLog (Compose f g) = FLog (Rep1 (Compose f g))
  findex = findexRep
  {-# inline findex #-}

instance (Distributive f, FDistributive g) => FDistributive (Compose f g) where
  ftabulate = ftabulateRep
  {-# inline ftabulate #-}

instance (FIndexable f, FIndexable g) => FIndexable (Product f g) where
  type FLog (Product f g) = FLog (Rep1 (Product f g))
  findex = findexRep
  {-# inline findex #-}

instance (FDistributive f, FDistributive g) => FDistributive (Product f g) where
  ftabulate = ftabulateRep
  {-# inline ftabulate #-}

instance FIndexable Proxy
instance FDistributive Proxy

deriving newtype instance FIndexable f => FIndexable (Backwards f)
deriving newtype instance FIndexable f => FIndexable (Reverse f)
deriving newtype instance FIndexable f => FIndexable (Monoid.Alt f)
deriving newtype instance FIndexable f => FIndexable (Monoid.Ap f)

deriving newtype instance FDistributive f => FDistributive (Backwards f)
deriving newtype instance FDistributive f => FDistributive (Reverse f)
deriving newtype instance FDistributive f => FDistributive (Monoid.Alt f)
deriving newtype instance FDistributive f => FDistributive (Monoid.Ap f)

instance FIndexable (F1 a) where
  type FLog (F1 a) = (:~:) a
  findex = \f Refl -> runF1 f
  {-# inline findex #-}

instance FDistributive (F1 a) where
  fscatter = \k f w -> F1 $ k $ ffmap f w
  ftabulate = \f -> F1 (f Refl)
  {-# inline fscatter #-}
  {-# inline ftabulate #-}

instance FIndexable (NT f) where
  type FLog (NT f) = f
  findex = runNT
  {-# inline findex #-}

instance FDistributive (NT f) where
  fscatter = fscatterDefault
  ftabulate = NT
  {-# inline ftabulate #-}
  {-# inline fscatter #-}

instance FIndexable Limit where
  type FLog Limit = U1
  findex f = const $ runLimit f
  {-# inline findex #-}

instance FDistributive Limit where
  fscatter = \k f w -> Limit $ k $ ffmap (\x -> F1 $ runLimit $ f x) w
  ftabulate = \f -> Limit $ f U1
  {-# inline ftabulate #-}
  {-# inline fscatter #-}

-- TODO: FLog (F2 a b) = Index '[a,b], etc.

instance FIndexable (F2 a b) where
  type FLog (F2 a b) = FLogarithm (F2 a b)
  findex = findexFLogarithm
  {-# inline findex #-}

instance FDistributive (F2 a b) where
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

instance FDistributive (F3 a b c) where
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

instance FDistributive (F4 a b c d) where
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

instance FDistributive (F5 a b c d e) where
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

instance (FDistributive f, FTraversable f) => FTraversable (FDist f) where
  ftraverse = \f -> fmap FDist . ftraverse f .# runFDist
  {-# inline ftraverse #-}

deriving newtype instance FIndexable f => FIndexable (FDist f)
deriving newtype instance FDistributive f => FDistributive (FDist f)

-- | A default definition for 'ffmap' from 'FFunctor' in terms of 'FDistributive'
ffmapFDist :: FDistributive f => (a ~> b) -> f a -> f b
ffmapFDist = \f -> fscatter (f .# (runF1 . runF1)) id .# F1
{-# inline ffmapFDist #-}

instance FDistributive f => FFunctor (FDist f) where
  ffmap = ffmapFDist
  {-# inline ffmap #-}

instance FDistributive f => FApply (FDist f) where
  fliftA2 = fliftA2FDist
  {-# inline fliftA2 #-}

-- | A default definition of 'fliftA2' from 'FApply' in terms of 'FDistributive'
fliftA2FDist :: FDistributive f => (forall x. a x -> b x -> c x) -> f a -> f b -> f c
fliftA2FDist = fliftD2
{-# inline fliftA2FDist #-}

fliftD2 :: FDistributive f => (forall x. a x -> b x -> c x) -> f a -> f b -> f c
fliftD2 = \f m n ->
  fdistrib (F2 m n) \(F2 (F1 m') (F1 n')) -> f m' n'
{-# inline fliftD2 #-}

fliftD3 :: FDistributive f => (forall x. a x -> b x -> c x -> d x) -> f a -> f b -> f c -> f d
fliftD3 = \f m n o ->
  fdistrib (F3 m n o) \(F3 (F1 m') (F1 n') (F1 o')) -> f m' n' o'
{-# inline fliftD3 #-}

fliftD4 :: FDistributive f => (forall x. a x -> b x -> c x -> d x -> e x) -> f a -> f b -> f c -> f d -> f e
fliftD4 = \f m n o p ->
  fdistrib (F4 m n o p) \(F4 (F1 m') (F1 n') (F1 o') (F1 p')) -> f m' n' o' p'
{-# inline fliftD4 #-}

fliftD5 :: FDistributive f => (forall x. a x -> b x -> c x -> d x -> e x -> r x) -> f a -> f b -> f c -> f d -> f e -> f r
fliftD5 = \f m n o p q ->
  fdistrib (F5 m n o p q) \(F5 (F1 m') (F1 n') (F1 o') (F1 p') (F1 q')) -> f m' n' o' p' q'
{-# inline fliftD5 #-}

instance FDistributive f => FApplicative (FDist f) where
  fpure = fpureFDist
  {-# inline fpure #-}

-- | A default definition of 'fpure' from 'FApplicative' in terms of 'FDistributive'
fpureFDist :: FDistributive f => (forall x. a x) -> f a
fpureFDist = \ax -> fscatter (\x -> runLimit (getConst x)) id $ Const $ Limit ax
-- fpureDist a = fdistrib Proxy \_ -> a
{-# inline fpureFDist #-}

faskFDist :: FDistributive f => f (FLog f)
faskFDist = ftabulate id
{-# noinline[0] faskFDist #-}

ftraceFDist :: FIndexable f => FLog f a -> f g -> g a
ftraceFDist = \x y -> findex y x

-- | We can convert a 'FLogarithm' of a 'FDistributive' 'FFunctor' to any choice
-- of 'FLog', as the two forms are canonically isomorphic.
--
-- @
-- 'findex' f . 'flogFromLogarithm' ≡ 'findexLogarithm' f
-- 'ftabulate' (f . 'flogFromLogarithm') ≡ 'ftabulateLogarithm' f
-- 'flogFromLogarithm' '.' 'flogToLogarithm' ≡ 'id'
-- 'flogToLogarithm' '.' 'flogFromLogarithm' ≡ 'id'
-- @
flogFromFLogarithm :: FDistributive f => FLogarithm f ~> FLog f
flogFromFLogarithm = \(FLogarithm f) -> f faskFDist
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
flogToFLogarithm = \f -> FLogarithm (ftraceFDist f)
{-# inline flogToFLogarithm #-}

-------------------------------------------------------------------------------
-- HKD
-------------------------------------------------------------------------------

type role HKD representational nominal nominal
newtype HKD (f :: Type -> Type) (x :: i) (a :: i -> Type) = HKD { runHKD :: f (a x) }

mapHKD :: (f (a x) -> g (b x)) -> HKD f x a -> HKD g x b
mapHKD = \f -> HKD #. f .# runHKD
{-# inline mapHKD #-}

type role DHKD representational nominal nominal
newtype DHKD w x f = DHKD { runDHKD :: w (HKD f x) }

type role Atkey representational nominal nominal
data Atkey a i j where
  Atkey :: a -> Atkey a k k

instance FFunctor w => FFunctor (DHKD w x) where
  ffmap f = DHKD #. ffmap (mapHKD f) .# runDHKD
  {-# inline ffmap #-}

instance Functor f => FFunctor (HKD f x) where
  ffmap = \f -> mapHKD (fmap f)
  {-# inline ffmap #-}

instance FunctorWithIndex i f => FFunctorWithIndex (Atkey i x) (HKD f x) where
  ifmap = \f -> mapHKD (imap (f . Atkey))
  {-# inline ifmap #-}

instance Foldable f => FFoldable (HKD f x) where
  ffoldMap = \f -> foldMap f .# runHKD
  {-# inline ffoldMap #-}

instance FoldableWithIndex i f => FFoldableWithIndex (Atkey i x) (HKD f x) where
  iffoldMap = \f -> ifoldMap (f . Atkey) .# runHKD
  {-# inline iffoldMap #-}

instance Traversable f => FTraversable (HKD f x) where
  ftraverse = \f -> fmap HKD . traverse f .# runHKD
  {-# inline ftraverse #-}

instance TraversableWithIndex i f => FTraversableWithIndex (Atkey i x) (HKD f x) where
  iftraverse = \f -> fmap HKD . itraverse (f . Atkey) .# runHKD
  {-# inline iftraverse #-}

instance Applicative f => FApply (HKD f x) where
  fliftA2 = \f (HKD fab) -> HKD #. liftA2 f fab .# runHKD
  {-# inline fliftA2 #-}

instance Applicative f => FApplicative (HKD f x) where
  fpure f = HKD $ pure f
  {-# inline fpure #-}

instance Indexable f => FIndexable (HKD f x) where
  type FLog (HKD f x) = Atkey (Log f) x
  findex = \(HKD fa) (Atkey lg) -> index fa lg
  {-# inline findex #-}

instance Distributive f => FDistributive (HKD f x) where
  fscatter = \k g w -> HKD $ distrib (DHKD (ffmap g w)) $ k . ffmap coerce .# runDHKD
  {-# inline fscatter #-}
  ftabulate = \f -> HKD $ tabulate (f . Atkey)
  {-# inline ftabulate #-}

instance Contravariant f => FContravariant (HKD f x) where
  fcontramap = \f -> HKD #. contramap f .# runHKD
  {-# inline fcontramap #-}

instance Divisible f => FSemidivisible (HKD f x) where
  fdivide = \f g -> HKD #. divide (\a -> case f a of (b :*: c) -> (b, c)) (runHKD g) .# runHKD
  {-# inline fdivide #-}

instance Divisible f => FDivisible (HKD f x) where
  fconquer = HKD conquer
  {-# inline fconquer #-}

instance Decidable f => FSemidecidable (HKD f x) where
  fchoose = \f g -> HKD #. choose (\a -> case f a of
    L1 x -> Left x
    R1 y -> Right y) (runHKD g) .# runHKD
  {-# inline fchoose #-}
  flose f = HKD (lose \x -> case f x of)
  {-# inline flose #-}

-------------------------------------------------------------------------------
-- LKD
-------------------------------------------------------------------------------

type role LKD representational nominal
newtype LKD f a = LKD { runLKD :: f (Const a) }

instance FFunctor f => Functor (LKD f) where
  fmap = \f -> LKD #. ffmap (Const #. f .# getConst) .# runLKD
  {-# inline fmap #-}

instance FFunctorWithIndex i f => FunctorWithIndex (Some i) (LKD f) where
  imap = \f -> LKD #. ifmap (\i -> Const #. f (Some i) .# getConst) .# runLKD

instance FFoldable f => Foldable (LKD f) where
  foldMap = \f -> ffoldMap (f .# getConst) .# runLKD
  {-# inline foldMap #-}

instance FFoldableWithIndex i f => FoldableWithIndex (Some i) (LKD f) where
  ifoldMap = \f -> iffoldMap (\i -> f (Some i) .# getConst) .# runLKD
  {-# inline ifoldMap #-}

instance FTraversable f => Traversable (LKD f) where
  traverse = \f -> fmap LKD . ftraverse (fmap Const . f .# getConst) .# runLKD
  {-# inline traverse #-}

instance FTraversableWithIndex i f => TraversableWithIndex (Some i) (LKD f) where
  itraverse = \f -> fmap LKD . iftraverse (\i -> fmap Const . f (Some i) .# getConst) .# runLKD
  {-# inline itraverse #-}

instance FContravariant f => Contravariant (LKD f) where
  contramap = \f -> LKD #. fcontramap (Const #. f .# getConst) .# runLKD
  {-# inline contramap #-}

instance FDivisible f => Divisible (LKD f) where
  divide = \f g -> LKD #. fdivide
    (\(Const a) -> case f a of
      (b,c) -> Const b :*: Const c
    )
    (runLKD g) .# runLKD
  {-# inline divide #-}
  conquer = LKD fconquer
  {-# inline conquer #-}

instance FDecidable f => Decidable (LKD f) where
  choose = \f g -> LKD #. fchoose
    (\(Const a) -> case f a of
      Left b -> L1 (Const b)
      Right b -> R1 (Const b)) (runLKD g) .# runLKD
  {-# inline choose #-}

  lose = \f -> LKD $ flose (absurd . f .# getConst)
  {-# inline lose #-}

-- Assumes FApplicative is FApplicative
instance FApplicative f => Applicative (LKD f) where
  (<*>) = \(LKD fab) -> LKD #. fliftA2 coerce fab .# runLKD
  {-# inline (<*>) #-}
  pure = \a -> LKD $ fpure (Const a)
  {-# inline pure #-}

type role DLKD representational nominal
newtype DLKD w f = DLKD { runDLKD :: w (LKD f) }

instance FFunctor w => FFunctor (DLKD w) where
  ffmap = \f -> DLKD #. ffmap (LKD #. f .# runLKD) .# runDLKD
  {-# inline ffmap #-}

instance FIndexable f => Indexable (LKD f) where
  type Log (LKD f) = Some (FLog f)
  index = \fa (Some lg) -> getConst (findex (runLKD fa) lg)
  {-# inline index #-}

instance FDistributive f => Distributive (LKD f) where
  scatter = \k g -> LKD . fscatter (Const #. k .  ffmap coerce .# runDLKD) id . DLKD . ffmap g
  {-# inline scatter #-}
  tabulate = \f -> LKD $ ftabulate (Const #. f . Some)
  {-# inline tabulate #-}

lowerLogarithm :: FLogarithm f x -> Logarithm (LKD f)
lowerLogarithm = \(FLogarithm f) -> Logarithm $ getConst #. f .# runLKD
{-# inline lowerLogarithm #-}

liftLogarithm :: FDistributive f => Logarithm (LKD f) -> Some (FLogarithm f)
liftLogarithm = \(Logarithm f) -> f $ LKD $ ftabulateFLogarithm (Const #. Some)
{-# inline liftLogarithm #-}

instance (FTraversable f, FDistributive f) => Eq (FLogarithm f a) where
  (==) = on (==) lowerLogarithm
  {-# inline (==) #-}

instance (FTraversable f, FDistributive f) => Ord (FLogarithm f a) where
  compare = on compare lowerLogarithm
  {-# inline compare #-}

-- safer than it looks
instance (FTraversable f, FDistributive f) => GEq (FLogarithm f) where
  geq = \x y ->
    if lowerLogarithm x == lowerLogarithm y
    then Just (unsafeCoerce Refl)
    else Nothing
  {-# inline geq #-}

geqFLog :: forall f a b. (FDistributive f, FTraversable f) => FLog f a -> FLog f b -> Maybe (a :~: b)
geqFLog x y = geq (flogFPath @f x) (flogFPath @f y)
{-# inline geqFLog #-}

gcompareFLog :: forall f a b. (FDistributive f, FTraversable f) => FLog f a -> FLog f b -> GOrdering a b
gcompareFLog x y = gcompare (flogFPath @f x) (flogFPath @f y)
{-# inline gcompareFLog #-}

instance (FTraversable f, FDistributive f) => TestEquality (FLogarithm f) where
  testEquality = geq
  {-# inline testEquality #-}

instance (FTraversable f, FDistributive f) => TestCoercion (FLogarithm f) where
  testCoercion = \x y -> repr <$> geq x y
  {-# inline testCoercion #-}

instance (FTraversable f, FDistributive f) => GCompare (FLogarithm f) where
  gcompare = \x y -> case compare (lowerLogarithm x) (lowerLogarithm y) of
    LT -> GLT
    EQ -> unsafeCoerce GEQ
    GT -> GGT
  {-# inline gcompare #-}

flogFPath :: forall f. (FDistributive f, FTraversable f) => FLog f ~> FPath Proxy
flogFPath = findex $ runTrail (ftraverse fend $ fpureFDist @f Proxy) id
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

_flog :: (FTraversable t, FDistributive t) => FLog t a -> Lens' (t f) (f a)
_flog = \i a2ga tf ->
  case findex (runTrail (ftraverse fend tf) id) i of
    FPath a p -> a2ga a <&> \a' -> runEvil (ftraverse (\a'' -> Evil a'' (const (unsafeCoerce a'))) tf) p
{-# inline _flog #-}

-- | Construct the lens for a logarithm using @'GEq' ('FLog' t)@ instead of with @'FTraversable' t@
_flogGEq :: (FDistributive t, GEq (FLog t)) => FLog t a -> Lens' (t f) (f a)
_flogGEq = \i a2ga fa -> a2ga (findex fa i) <&> \a' -> ifmapFDist (\j a -> case geq i j of
  Just Refl -> a'
  Nothing -> a) fa
{-# inline _flogGEq #-}

instance (FDistributive f, FLog f ~ i) => FFunctorWithIndex i (FDist f) where
  ifmap = ifmapFDist
  {-# inline ifmap #-}

ifmapFDist
  :: forall f a b. FDistributive f
  => (forall x. FLog f x -> a x -> b x) -> f a -> f b
ifmapFDist = \f -> fliftA2FDist f is
  where is = faskFDist :: f (FLog f)
{-# inline ifmapFDist #-}

instance (FDistributive f, FFoldable f, FLog f ~ i) => FFoldableWithIndex i (FDist f) where
  iffoldMap = iffoldMapFDist
  {-# inline iffoldMap #-}

-- | A default definition for 'ifoldMap' from @FoldableWithIndex@ in terms of 'Distributive'
iffoldMapFDist
  :: forall f m a.
     (FDistributive f, FFoldable f, Monoid m)
  => (forall x. FLog f x -> a x -> m) -> f a -> m
iffoldMapFDist = \f -> ffoldMap getConst . ifmapFDist (\i -> Const #. f i)
{-# inline iffoldMapFDist #-}

instance (FDistributive f, FTraversable f, FLog f ~ i) => FTraversableWithIndex i (FDist f) where
  iftraverse = iftraverseFDist
  {-# inline iftraverse #-}

iftraverseFDist
  :: forall f m a b.
     (FDistributive f, FTraversable f, Applicative m)
  => (forall x. FLog f x -> a x -> m (b x)) -> f a -> m (f b)
iftraverseFDist = \f -> ftraverse getCompose . ifmapFDist (\i -> Compose #. f i)
{-# inline iftraverseFDist #-}

instance FIndexable (FConstrained p) where
  type FLog (FConstrained p) = Dict1 p
  findex = \(FConstrained x) Dict1 -> x

instance FDistributive (FConstrained p) where
  fscatter = \k f (ffmap f -> w) -> FConstrained $ k $ ffmap (\(FConstrained x) -> F1 x) w
  ftabulate = \f -> FConstrained $ f Dict1

class FAll (p :: i -> Constraint) (f :: (i -> Type) -> Type) where
  fall :: f (Dict1 p)
  default fall :: (Generic1 f, FAll p (Rep1 f)) => f (Dict1 p)
  fall = to1 fall

instance (FAll p f, FAll p g) => FAll p (f :*: g) where
  fall = fall :*: fall

instance (Distributive f, FAll p g) => FAll p (f :.: g) where
  fall = Comp1 $ pureDist fall

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

instance (Distributive f, FAll p g) => FAll p (Compose f g)

instance (FAll p f, FAll p g) => FAll p (Product f g)

-- this is arguably any existential constraint
instance (forall a. p a) => FAll p Some where fall = Some Dict1
instance (forall a. p a) => FAll p Limit where fall = Limit Dict1
instance (forall a. q a => p a) => FAll p (FConstrained q) where
  fall = FConstrained Dict1

fliftA2W :: (FDistributive f, FFunctor w) => (forall x. a x -> w (F1 x) -> r x) -> f a -> w f -> f r
fliftA2W f fa w = fdistrib (F1 fa :*: w) \(F1 (F1 a) :*: w') -> f a w'

cfdistrib
  :: forall i (p :: i -> Constraint) (f :: (i -> Type) -> Type) (r :: i -> Type) w.
     (FAll p f, FFunctor w, FDistributive f)
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

instance (Distributive w, Foldable w) => DefaultFEq (w :: Type -> Type) where
  feqDefault = \x -> and . liftD2 (==) x

instance (FDistributive w, FFoldable w, FAll EqC w) => DefaultFEq (w :: (k -> Type) -> Type) where
  feqDefault = \x y ->
    Monoid.getAll $
    ffoldMap getConst $
    fliftD3
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
-- In any of these cases 'tabulateRep/indexRep and defining
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

type role AppCompose representational nominal nominal
newtype AppCompose w g f = AppCompose { runAppCompose :: w (f :.: g) }
instance FFunctor w => FFunctor (AppCompose w g) where
  ffmap f = AppCompose #. ffmap (Comp1 #. f .# unComp1) .# runAppCompose
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
  deriving anyclass (Indexable, Distributive)
  deriving (Eq1,Ord1,Applicative, Monad, MonadFix, MonadZip) via Dist V2
  deriving (Eq,Ord,Num,Fractional,Floating,Semigroup,Monoid) via Dist V2 a

instance Show1 V2 where
  liftShowsPrec f _ d (V2 a b) = showParen (d > 10) $ showString "V2 " . f 11 a . showChar ' ' . f 11 b

class 
  ( Traversable f
  , Distributive f
  , IsJust (KnownSize f) ~ 'True
  , KnownNat (Size f)
  ) => FiniteDistributive f

instance 
  ( Traversable f
  , Distributive f
  , IsJust (KnownSize f) ~ 'True
  , KnownNat (Size f)
  ) => FiniteDistributive f

type Size f = FromJust (KnownSize f)
type Indices f = FromJust (KnownIndices f)

type LogFin f = Fin (Size f)
type FLogIndex f = Index (Indices f)

type HasLogFin f = Log f == LogFin f

lie :: a
lie = error "Data.Distributive.Internal: logic error. index out of bounds or invalid Size f"

class DefaultIndexFin' (b :: Bool) (f :: Type -> Type) where
  indexFinDefault :: f a -> LogFin f -> a

instance (Log f ~ LogFin f, Distributive f) => DefaultIndexFin' 'True f where
  indexFinDefault = index
  {-# inline indexFinDefault #-}

type f /~ g = (f == g) ~ 'False

instance (Log f /~ LogFin f, FiniteDistributive f) => DefaultIndexFin' 'False f where
  indexFinDefault = \ f (Fin i) ->
    fromMaybe lie $
    Monoid.getFirst $
    fold $
    liftD2
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

instance (Log f ~ LogFin f, Distributive f) => DefaultTabulateFin' 'True f where
  tabulateFinDefault = tabulate
  {-# inline tabulateFinDefault #-}

instance (Log f /~ LogFin f, FiniteDistributive f) => DefaultTabulateFin' 'False f where
  tabulateFinDefault f =
    case mapAccumL (\n () -> (n + 1, f $ UnsafeFin n)) 0 (pureDist ()) of
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
