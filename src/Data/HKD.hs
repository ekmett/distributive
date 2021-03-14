{-# language CPP #-}
{-# language FlexibleContexts #-}
{-# language FlexibleInstances #-}
{-# language GADTs #-}
{-# language MultiParamTypeClasses #-}
{-# language PolyKinds #-}
{-# language RankNTypes #-}
{-# language ScopedTypeVariables #-}
{-# language Trustworthy #-}
{-# language TypeOperators #-}
#if !defined(HLINT) && MIN_VERSION_base(4,10,0) && __GLASGOW_HASKELL__ >= 708
{-# language LambdaCase #-}
{-# language EmptyCase #-}
#endif
-- |
-- Copyright :  (c) 2019 Edward Kmett, 2019 Oleg Grenrus
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Oleg Grenrus <oleg.grenrus@iki.fi>
-- Stability :  experimental
-- Portability: non-portable
--
-- "Higher-Kinded Data" such as it is
module Data.HKD
(
-- * "Natural" transformation
   type (~>)
-- * Functor
, FFunctor(..)
-- * Contravariant
, FContravariant(..)
-- * Foldable
, FFoldable(..)
, flength
, ftraverse_
, ffor_
-- * Traversable
, FTraversable(..)
, ffmapDefault
, ffoldMapDefault
, ffor
, fsequence
-- ** Generic derivation
, gftraverse
-- * Zip & Repeat
, FZip (..)
, FRepeat (..)
-- ** Generic derivation
, gfzipWith
, gfrepeat
-- * Higher kinded data
-- | See also "Data.Some" in @some@ package. @hkd@ provides instances for it.
, Logarithm(..)
, Tab(..)
, indexLogarithm
, Element(..)
, NT(..)
, Limit(..)
) where

#if MIN_VERSION_base(4,9,0)
import Data.Kind (Type)
#else
#define Type *
#endif

import Control.Applicative
import qualified Data.Monoid as Monoid
import Data.Semigroup (Semigroup (..))
import Data.Proxy (Proxy (..))
import Data.Functor.Identity (Identity (..))
import Data.Monoid (Monoid (..))

import GHC.Generics
import Data.Functor.Confusing

-- In older base:s types aren't PolyKinded
#if MIN_VERSION_base(4,9,0)
import Data.Coerce (Coercible, coerce)
import Data.Functor.Compose (Compose (..))
import Data.Functor.Product (Product (..))
import Data.Functor.Sum (Sum (..))
#endif

import Data.Some.GADT (Some (..), mapSome, foldSome)
import qualified Data.Some.Newtype as N
import qualified Data.Some.Church as C

#if MIN_VERSION_base(4,9,0)
(#.) :: Coercible b c => (b -> c) -> (a -> b) -> a -> c
(#.) _ = coerce

(.#) :: Coercible a b => (b -> c) -> (a -> b) -> a -> c
(.#) f _ = coerce f

infixr 9 #.
infixr 8 .#
#endif

-------------------------------------------------------------------------------
-- wiggly arrow
-------------------------------------------------------------------------------

type f ~> g = forall a. f a -> g a

-------------------------------------------------------------------------------
-- FFunctor
-------------------------------------------------------------------------------

class FFunctor (t :: (k -> Type) -> Type) where
  ffmap :: (f ~> g) -> t f -> t g

instance FFunctor Proxy where
  ffmap _ Proxy = Proxy

#if MIN_VERSION_base(4,9,0)
instance FFunctor (Const a) where
  ffmap _ (Const a) = Const a

instance (Functor f, FFunctor g) => FFunctor (Compose f g) where
  ffmap f = Compose #. fmap (ffmap f) .# getCompose

instance (FFunctor f, FFunctor g) => FFunctor (Product f g) where
  ffmap f (Pair g h) = Pair (ffmap f g) (ffmap f h)

instance (FFunctor f, FFunctor g) => FFunctor (Sum f g) where
  ffmap f (InL g) = InL (ffmap f g)
  ffmap f (InR h) = InR (ffmap f h)
#endif

#if MIN_VERSION_base(4,10,0)
instance FFunctor (K1 i a) where
  ffmap _ = coerce

instance FFunctor f => FFunctor (M1 i c f) where
  ffmap f = M1 #. ffmap f .# unM1

instance FFunctor f => FFunctor (Rec1 f) where
  ffmap f = Rec1 #. ffmap f .# unRec1

instance FFunctor U1 where
  ffmap _ U1 = U1

instance FFunctor V1 where
#ifndef HLINT
  ffmap _ = \case
#endif

instance (Functor f, FFunctor g) => FFunctor (f :.: g) where
  ffmap f = Comp1 #. fmap (ffmap f) .# unComp1

instance (FFunctor f, FFunctor g) => FFunctor (f :*: g) where
  ffmap f (g :*: h) = ffmap f g :*: ffmap f h

instance (FFunctor f, FFunctor g) => FFunctor (f :+: g) where
  ffmap f (L1 g) = L1 (ffmap f g)
  ffmap f (R1 h) = R1 (ffmap f h)
#endif

-------------------------------------------------------------------------------
-- FFoldable
-------------------------------------------------------------------------------

class FFoldable (t :: (k -> Type) -> Type) where
  ffoldMap :: Monoid.Monoid m => (forall a. f a -> m) -> t f -> m

  flengthAcc :: Int -> t f -> Int
  flengthAcc acc t = acc + Monoid.getSum (ffoldMap (\_ -> Monoid.Sum 1) t)

flength :: FFoldable t => t f -> Int
flength = flengthAcc 0

ftraverse_ :: (FFoldable t, Applicative m) => (forall a. f a -> m b) -> t f -> m ()
ftraverse_ k tf = N.withSome (ffoldMap (N.mkSome . k) tf) (() <$)

ffor_ :: (FFoldable t, Applicative m) => t f -> (forall a. f a -> m b) -> m ()
ffor_ tf k = ftraverse_ k tf

instance FFoldable Proxy where
  ffoldMap _ = Data.Monoid.mempty
  flengthAcc = const

#if MIN_VERSION_base(4,9,0)
instance FFoldable (Const a) where
  ffoldMap _ = mempty
  flengthAcc = const

instance (Foldable f, FFoldable g) => FFoldable (Compose f g) where
  ffoldMap f = foldMap (ffoldMap f) .# getCompose

instance (FFoldable f, FFoldable g) => FFoldable (Product f g) where
  ffoldMap f (Pair g h) = ffoldMap f g `mappend` ffoldMap f h
  flengthAcc f (Pair g h) = f `flengthAcc` g `flengthAcc` h

instance (FFoldable f, FFoldable g) => FFoldable (Sum f g) where
  ffoldMap f (InL g) = ffoldMap f g
  ffoldMap f (InR h) = ffoldMap f h
#endif

#if MIN_VERSION_base(4,10,0)
instance FFoldable V1 where
#ifndef HLINT
  ffoldMap _ = \case
  flengthAcc _ = \case
#endif

instance FFoldable (K1 i a) where
  ffoldMap _ = mempty
  flengthAcc = const

instance FFoldable f => FFoldable (M1 i c f) where
  ffoldMap f = ffoldMap f .# unM1
  flengthAcc n = flengthAcc n .# unM1

instance FFoldable f => FFoldable (Rec1 f) where
  ffoldMap f = ffoldMap f .# unRec1
  flengthAcc n = flengthAcc n .# unRec1

instance FFoldable U1 where
  ffoldMap _ = mempty
  flengthAcc = const

instance (Foldable f, FFoldable g) => FFoldable (f :.: g) where
  ffoldMap f = foldMap (ffoldMap f) .# unComp1

instance (FFoldable f, FFoldable g) => FFoldable (f :*: g) where
  ffoldMap f (g :*: h) = ffoldMap f g `mappend` ffoldMap f h
  flengthAcc acc (g :*: h) = acc `flengthAcc` g `flengthAcc` h

instance (FFoldable f, FFoldable g) => FFoldable (f :+: g) where
  ffoldMap f (L1 g) = ffoldMap f g
  ffoldMap f (R1 h) = ffoldMap f h
  flengthAcc acc (L1 g) = flengthAcc acc g
  flengthAcc acc (R1 g) = flengthAcc acc g
#endif

-------------------------------------------------------------------------------
-- FTraversable
-------------------------------------------------------------------------------

class (FFoldable t, FFunctor t) => FTraversable (t :: (k -> Type) -> Type) where
  ftraverse :: Applicative m => (forall a. f a -> m (g a)) -> t f -> m (t g)

ffmapDefault :: FTraversable t =>  (f ~> g) -> t f -> t g
ffmapDefault k = runIdentity . ftraverse (Identity . k)

ffoldMapDefault :: (FTraversable t, Monoid m) =>  (forall a. f a -> m) -> t f -> m
ffoldMapDefault k = getConst . ftraverse (Const . k)

ffor :: (FTraversable t, Applicative m) => t f -> (forall a. f a -> m (g a)) -> m (t g)
ffor tf k = ftraverse k tf

fsequence :: (FTraversable t, Applicative f) => t f -> f (t Identity)
fsequence = ftraverse (fmap Identity)

instance FTraversable Proxy where
  ftraverse _ Proxy = pure Proxy

#if MIN_VERSION_base(4,9,0)
instance FTraversable (Const a) where
  ftraverse _ = pure .# (Const . getConst)

instance (Traversable f, FTraversable g) => FTraversable (Compose f g) where
  ftraverse f = fmap Compose . traverse (ftraverse f) .# getCompose

instance (FTraversable f, FTraversable g) => FTraversable (Product f g) where
  ftraverse f (Pair g h) = Pair <$> ftraverse f g <*> ftraverse f h

instance (FTraversable f, FTraversable g) => FTraversable (Sum f g) where
  ftraverse f (InL g) = InL <$> ftraverse f g
  ftraverse f (InR h) = InR <$> ftraverse f h
#endif

#if MIN_VERSION_base(4,10,0)
instance FTraversable U1 where
  ftraverse _ U1 = pure U1

instance FTraversable V1 where
#ifndef HLINT
  ftraverse _ = \case
#endif

instance FTraversable f => FTraversable (M1 i c f) where
  ftraverse f = fmap M1 . ftraverse f .# unM1

instance FTraversable f => FTraversable (Rec1 f) where
  ftraverse f = fmap Rec1 . ftraverse f .# unRec1

instance FTraversable (K1 i a) where
  ftraverse _ = pure .# (K1 . unK1)

instance (Traversable f, FTraversable g) => FTraversable (f :.: g) where
  ftraverse f = fmap Comp1 . traverse (ftraverse f) .# unComp1

instance (FTraversable f, FTraversable g) => FTraversable (f :*: g) where
  ftraverse f (g :*: h) = (:*:) <$> ftraverse f g <*> ftraverse f h

instance (FTraversable f, FTraversable g) => FTraversable (f :+: g) where
  ftraverse f (L1 g) = L1 <$> ftraverse f g
  ftraverse f (R1 h) = R1 <$> ftraverse f h
#endif

-------------------------------------------------------------------------------
-- FZip
-------------------------------------------------------------------------------

class FFunctor t => FZip t where
  fzipWith :: (forall x. f x -> g x -> h x) -> t f -> t g -> t h

class FZip t => FRepeat t where
  frepeat :: (forall x. f x) -> t f

instance FZip Proxy where
  fzipWith _ _ _ = Proxy

instance FRepeat Proxy where
  frepeat _ = Proxy

instance FZip (Element a) where
  fzipWith f (Element x) (Element y) = Element (f x y)

instance FRepeat (Element a) where
  frepeat x = Element x

instance FZip (NT f) where
  fzipWith f (NT g) (NT h) = NT $ \x -> f (g x) (h x)

instance FRepeat (NT a) where
  frepeat x = NT $ \_ -> x

instance FZip Limit where
  fzipWith f (Limit x) (Limit y) = Limit (f x y)

instance FRepeat Limit where
  frepeat x = Limit x

#if MIN_VERSION_base(4,9,0)
instance Data.Semigroup.Semigroup a => FZip (Const a) where
  fzipWith _ (Const a) (Const b) = Const (a <> b)

instance (Monoid a, Semigroup a) => FRepeat (Const a) where
  frepeat _ = Const mempty

instance (FZip f, FZip g) => FZip (Product f g) where
  fzipWith f (Pair x y) (Pair x' y') = Pair (fzipWith f x x') (fzipWith f y y')

instance (FRepeat f, FRepeat g) => FRepeat (Product f g) where
  frepeat x = Pair (frepeat x) (frepeat x)

-- | We only need an 'Apply' part of an 'Applicative'.
instance (Applicative f, FZip g) => FZip (Compose f g) where
  fzipWith f (Compose x) (Compose y) = Compose (liftA2 (fzipWith f) x y)

instance (Applicative f, FRepeat g) => FRepeat (Compose f g) where
  frepeat x = Compose (pure (frepeat x))
#endif

#if MIN_VERSION_base(4,10,0)
instance FZip U1 where
  fzipWith _ _ _ =  U1

instance FRepeat U1 where
  frepeat _ = U1

instance FZip V1 where
  fzipWith _ x _ = case x of

instance FZip f => FZip (M1 i c f) where
  fzipWith f (M1 x) (M1 y) = M1 $ fzipWith f x y

instance FZip f => FZip (Rec1 f) where
  fzipWith f (Rec1 x) (Rec1 y) = Rec1 $ fzipWith f x y

instance Data.Semigroup.Semigroup a => FZip (K1 i a) where
  fzipWith _ (K1 a) (K1 b) = K1 (a <> b)

instance (Monoid a, Semigroup a) => FRepeat (K1 i a) where
  frepeat _ = K1 mempty

instance FRepeat f => FRepeat (M1 i c f) where
  frepeat x = M1 $ frepeat x

instance FRepeat f => FRepeat (Rec1 f) where
  frepeat x = Rec1 $ frepeat x

instance (FZip f, FZip g) => FZip (f :*: g) where
  fzipWith f (x :*: y) (x' :*: y') = fzipWith f x x' :*: fzipWith f y y'

instance (FRepeat f, FRepeat g) => FRepeat (f :*: g) where
  frepeat x = frepeat x :*: frepeat x

-- | We only need an 'Apply' part of an 'Applicative'.
instance (Applicative f, FZip g) => FZip (f :.: g) where
  fzipWith f (Comp1 x) (Comp1 y) = Comp1 (liftA2 (fzipWith f) x y)

instance (Applicative f, FRepeat g) => FRepeat (f :.: g) where
  frepeat x = Comp1 (pure (frepeat x))
#endif

-------------------------------------------------------------------------------
-- FContravariant
-------------------------------------------------------------------------------

class FContravariant (t :: (k -> Type) -> Type) where
  fcontramap :: (f ~> g) -> t g -> t f

instance FContravariant Proxy where
  fcontramap _ Proxy = Proxy

#if MIN_VERSION_base(4,9,0)
instance FContravariant (Const a) where
  fcontramap _ (Const a) = Const a

instance (Functor f, FContravariant g) => FContravariant (Compose f g) where
  fcontramap f = Compose #. fmap (fcontramap f) .# getCompose

instance (FContravariant f, FContravariant g) => FContravariant (Product f g) where
  fcontramap f (Pair g h) = Pair (fcontramap f g) (fcontramap f h)

instance (FContravariant f, FContravariant g) => FContravariant (Sum f g) where
  fcontramap f (InL g) = InL (fcontramap f g)
  fcontramap f (InR h) = InR (fcontramap f h)
#endif

#if MIN_VERSION_base(4,10,0)
instance FContravariant (K1 i a) where
  fcontramap _ = coerce

instance FContravariant f => FContravariant (M1 i c f) where
  fcontramap f = M1 #. fcontramap f .# unM1

instance FContravariant f => FContravariant (Rec1 f) where
  fcontramap f = Rec1 #. fcontramap f .# unRec1

instance FContravariant U1 where
  fcontramap _ U1 = U1

instance FContravariant V1 where
#ifndef HLINT
  fcontramap _ = \case
#endif

instance (Functor f, FContravariant g) => FContravariant (f :.: g) where
  fcontramap f = Comp1 #. fmap (fcontramap f) .# unComp1

instance (FContravariant f, FContravariant g) => FContravariant (f :*: g) where
  fcontramap f (g :*: h) = fcontramap f g :*: fcontramap f h

instance (FContravariant f, FContravariant g) => FContravariant (f :+: g) where
  fcontramap f (L1 g) = L1 (fcontramap f g)
  fcontramap f (R1 h) = R1 (fcontramap f h)
#endif

-------------------------------------------------------------------------------
-- distributive utilities
-------------------------------------------------------------------------------

-- | A logarithm.
--
-- Recall that function arrow, @->@ is an exponential object. If we take @f = (->) r@, then
--
-- @
-- 'Logarithm' ((->) r) ≅ forall a. (r -> a) -> a ≅ r
-- @
--
-- and this works for all 'Distributive' / 'Representable' functors.
--
newtype Logarithm f = Logarithm { runLogarithm :: forall a. f a -> a }

indexLogarithm :: f a -> Logarithm f -> a
indexLogarithm fa (Logarithm fa2a) = fa2a fa

instance FContravariant Logarithm where
  fcontramap f g = Logarithm (runLogarithm g . f)

-- | Tabulation.
newtype Tab a f = Tab { runTab :: Logarithm f -> a }

instance FFunctor (Tab a) where
  ffmap f g = Tab (runTab g . fcontramap f)

-------------------------------------------------------------------------------
-- Elements
-------------------------------------------------------------------------------

-- | Element in @f@
newtype Element a f = Element { runElement :: f a }

instance FFunctor (Element a) where
  ffmap f (Element fa) = Element (f fa)

instance FFoldable (Element a) where
  ffoldMap f (Element fa) = f fa
  flengthAcc acc _ = acc + 1

instance FTraversable (Element a) where
  ftraverse f (Element g) = Element <$> f g

-------------------------------------------------------------------------------
-- "natural" transformations via parametricity
-------------------------------------------------------------------------------

-- | Newtyped "natural" transformation
newtype NT f g = NT { runNT :: f ~> g }

instance FFunctor (NT f) where
  ffmap f (NT g) = NT (f . g)

-------------------------------------------------------------------------------
-- Some
-------------------------------------------------------------------------------

instance FFunctor Some where
  ffmap = mapSome

instance FFoldable Some where
  ffoldMap = foldSome
  flengthAcc len _ = len + 1

instance FTraversable Some where
  ftraverse f (Some m) = Some <$> f m

instance FFunctor N.Some where
  ffmap = N.mapSome

instance FFoldable N.Some where
  ffoldMap = N.foldSome
  flengthAcc len _ = len + 1

instance FTraversable N.Some where
  ftraverse f x = N.withSome x $ \x' -> N.mkSome <$> f x'

instance FFunctor C.Some where
  ffmap = C.mapSome

instance FFoldable C.Some where
  ffoldMap = C.foldSome
  flengthAcc len _ = len + 1

instance FTraversable C.Some where
  ftraverse f x = C.withSome x $ \x' -> C.mkSome <$> f x'

-------------------------------------------------------------------------------
-- Limit
-------------------------------------------------------------------------------

newtype Limit f = Limit { runLimit :: forall a. f a }

instance FFunctor Limit where
  ffmap f (Limit g) = Limit (f g)

instance FFoldable Limit where
  ffoldMap f (Limit g) = f g
  flengthAcc len _ = len + 1

-------------------------------------------------------------------------------
-- Generic ftraverse
-------------------------------------------------------------------------------

-- | Generically derive 'ftraverse'.
--
-- Simple usage:
--
-- @
-- data Record f = Record
--     { fieldInt    :: f Int
--     , fieldString :: f String
--     , fieldSome   :: 'Some' f
--     }
--   deriving ('Generic')
--
-- instance 'FFunctor'     Record where 'ffmap'     = 'ffmapDefault'
-- instance 'FFoldable'    Record where 'ffoldMap'  = 'ffoldMapDefault'
-- instance 'FTraversable' Record where 'ftraverse' = 'gftraverse'
-- @

gftraverse
  :: forall t f g m. (Applicative m, Generic (t f), Generic (t g), GFTraversable (Curried (Yoneda m)) f g (Rep (t f)) (Rep (t g)))
  => (forall a. f a -> m (g a))
  -> t f
  -> m (t g)
gftraverse = fconfusing impl
  where
  impl :: FLensLike (Curried (Yoneda m)) (t f) (t g) f g
  impl nt = fmap to . gftraverse0 nt . from
{-# INLINE gftraverse #-}

class GFTraversable m f g tf tg where
  gftraverse0 :: (forall a. f a -> m (g a)) -> tf () -> m (tg ())

instance (i ~ D, i' ~ D, Functor m, GFTraversable1 m f g h h') => GFTraversable m f g (M1 i c h) (M1 i' c' h') where
  gftraverse0 nt = fmap M1 . gftraverse1 nt . unM1
  {-# INLINE gftraverse0 #-}

class GFTraversable1 m f g tf tg where
  gftraverse1 :: (forall a. f a -> m (g a)) -> tf () -> m (tg ())

instance GFTraversable1 m f g V1 V1 where
  gftraverse1 _ x = x `seq` error "Void is conjured"
  {-# INLINE gftraverse1 #-}

instance (Applicative m, GFTraversable1 m f g x x', GFTraversable1 m f g y y') => GFTraversable1 m f g (x :+: y) (x' :+: y') where
  gftraverse1 nt (L1 x) = fmap L1 (gftraverse1 nt x)
  gftraverse1 nt (R1 y) = fmap R1 (gftraverse1 nt y)
  {-# INLINE gftraverse1 #-}

instance (i ~ C, i' ~ C, Functor m, GFTraversable2 m f g h h') => GFTraversable1 m f g (M1 i c h) (M1 i' c' h') where
  gftraverse1 nt = fmap M1 . gftraverse2 nt . unM1
  {-# INLINE gftraverse1 #-}

class GFTraversable2 m f g tf tg where
  gftraverse2 :: (forall a. f a -> m (g a)) -> tf () -> m (tg ())

instance Applicative m  => GFTraversable2 m f g U1 U1 where
  gftraverse2 _ _ = pure U1
  {-# INLINE gftraverse2 #-}

instance (i ~ S, i' ~ S, Functor m, GFTraversable2 m f g h h') => GFTraversable2 m f g (M1 i c h) (M1 i' c' h') where
  gftraverse2 nt = fmap M1 . gftraverse2 nt . unM1
  {-# INLINE gftraverse2 #-}

instance (Applicative m, GFTraversable2 m f g x x', GFTraversable2 m f g y y') => GFTraversable2 m f g (x :*: y) (x' :*: y') where
  gftraverse2 nt (x :*: y) = liftA2 (:*:) (gftraverse2 nt x) (gftraverse2 nt y)
  {-# INLINE gftraverse2 #-}

instance (f ~ f', g ~ g', x ~ x', i ~ R, i' ~ R, Functor m) => GFTraversable2 m f g (K1 i (f' x)) (K1 i' (g' x')) where
  gftraverse2 nt = fmap K1 . nt . unK1
  {-# INLINE gftraverse2 #-}

instance (f ~ f', g ~ g', t ~ t', i ~ R, i' ~ R, Applicative m, FTraversable t) => GFTraversable2 m f g (K1 i (t f')) (K1 i' (t' g')) where
  gftraverse2 nt = fmap K1 . ftraverse nt . unK1
  {-# INLINE gftraverse2 #-}


-------------------------------------------------------------------------------
-- Generic fzipWith
-------------------------------------------------------------------------------

-- | Generically derive 'fzipWith'.
--
-- Simple usage:
--
-- @
-- data Record f = Record
--     { fieldInt    :: f Int
--     , fieldString :: f String
--     }
--   deriving ('Generic')
--
-- instance 'FZip'    Record where 'fzipWith' = 'gfzipWith'
-- instance 'FRepeat' Record where 'frepeat'  = 'gfrepeat'
-- @

gfzipWith
  :: forall t f g h. (Generic (t f), Generic (t g), Generic (t h), GFZip f g h (Rep (t f)) (Rep (t g)) (Rep (t h)))
  => (forall a. f a -> g a -> h a)
  -> t f
  -> t g
  -> t h
gfzipWith nt x y = to (gfzipWith0 nt (from x) (from y))
{-# INLINE gfzipWith #-}

class GFZip f g h tf tg th where
  gfzipWith0 :: (forall a. f a -> g a -> h a) -> tf () -> tg () -> th ()

instance (i0 ~ D, i1 ~ D, i2 ~ D, GFZip1 f g h t0 t1 t2) => GFZip f g h (M1 i0 c0 t0) (M1 i1 c1 t1) (M1 i2 c2 t2) where
  gfzipWith0 nt x y = M1 (gfzipWith1 nt (unM1 x) (unM1 y))
  {-# INLINE gfzipWith0 #-}

class GFZip1 f g h tf tg th where
  gfzipWith1 :: (forall a. f a -> g a -> h a) -> tf () -> tg () -> th ()

instance GFZip1 f g h V1 V1 V1 where
  gfzipWith1 _ x _ = x `seq` error "Void is conjured"

instance (i0 ~ C, i1 ~ C, i2 ~ C, GFZip2 f g h t0 t1 t2) => GFZip1 f g h (M1 i0 c0 t0) (M1 i1 c1 t1) (M1 i2 c2 t2) where
  gfzipWith1 nt x y = M1 (gfzipWith2 nt (unM1 x) (unM1 y))
  {-# INLINE gfzipWith1 #-}

class GFZip2 f g h tf tg th where
  gfzipWith2 :: (forall a. f a -> g a -> h a) -> tf () -> tg () -> th ()

instance GFZip2 f g h U1 U1 U1 where
  gfzipWith2 _ _ _ = U1

instance (GFZip2 f g h tf tg th, GFZip2 f g h sf sg sh) => GFZip2 f g h (tf :*: sf) (tg :*: sg) (th :*: sh) where
  gfzipWith2 nt (x :*: y) (x' :*: y') = gfzipWith2 nt x x' :*: gfzipWith2 nt y y'
  {-# INLINE gfzipWith2 #-}

instance (i0 ~ S, i1 ~ S, i2 ~ S, GFZip2 f g h t0 t1 t2) => GFZip2 f g h (M1 i0 c0 t0) (M1 i1 c1 t1) (M1 i2 c2 t2) where
  gfzipWith2 nt x y = M1 (gfzipWith2 nt (unM1 x) (unM1 y))
  {-# INLINE gfzipWith2 #-}

instance (f ~ f', g ~ g', h ~ h', x0 ~ x1, x1 ~ x2, i0 ~ R, i1 ~ R, i2 ~ R) => GFZip2 f g h (K1 i0 (f' x0)) (K1 i1 (g' x1)) (K1 i2 (h' x2)) where
  gfzipWith2 nt (K1 x) (K1 y) = K1 (nt x y)

instance (f ~ f', g ~ g', h ~ h', t0 ~ t1, t1 ~ t2, i0 ~ R, i1 ~ R, i2 ~ R, FZip t0) => GFZip2 f g h (K1 i0 (t0 f')) (K1 i1 (t1 g')) (K1 i2 (t2 h')) where
  gfzipWith2 nt (K1 x) (K1 y) = K1 (fzipWith nt x y)

-------------------------------------------------------------------------------
-- Generic frepeat
-------------------------------------------------------------------------------

gfrepeat
  :: forall t f. (Generic (t f), GFRepeat f (Rep (t f)))
  => (forall x. f x)
  -> t f
gfrepeat x = to (gfrepeat0 x)

class GFRepeat f tf where
  gfrepeat0 :: (forall a. f a) -> tf ()

instance (i ~ D, GFRepeat1 g f) => GFRepeat g (M1 i c f) where
  gfrepeat0 x = M1 (gfrepeat1 x)

class GFRepeat1 f tf where
  gfrepeat1 :: (forall a. f a) -> tf ()

instance (i ~ C, GFRepeat2 g f) => GFRepeat1 g (M1 i c f) where
  gfrepeat1 x = M1 (gfrepeat2 x)

class GFRepeat2 f tf where
  gfrepeat2 :: (forall a. f a) -> tf ()

instance (i ~ S, GFRepeat2 g f) => GFRepeat2 g (M1 i c f) where
  gfrepeat2 x = M1 (gfrepeat2 x)

instance (GFRepeat2 f x, GFRepeat2 f y) => GFRepeat2 f (x :*: y) where
  gfrepeat2 x = gfrepeat2 x :*: gfrepeat2 x

instance GFRepeat2 f U1 where
  gfrepeat2 _ = U1

instance (i ~ R, f ~ f') => GFRepeat2 f (K1 i (f' x)) where
  gfrepeat2 x = K1 x

instance (i ~ R, f ~ f', FRepeat t) => GFRepeat2 f (K1 i (t f')) where
  gfrepeat2 x = K1 (frepeat x)
