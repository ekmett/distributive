{-# Language GeneralizedNewtypeDeriving #-}
{-# Language Trustworthy #-}

-- |
-- Copyright :  (c) 2021 Edward Kmett
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable
--
-- Contravariant "Higher-Kinded Data"

module Data.HKD.Contravariant
( FContravariant(..)
, FSemidivisible(..)
, FDivisible(..)
, fdivided
, fconquered
, fliftDiv
, FSemidecidable(..)
, FDecidable
, flost
, fchosen
, FSemideciding(..)
--, FDeciding(..)
-- * Types
, FEquivalence(..)
, FComparison(..)
, FOp(..)
) where

import Control.Applicative
import Control.Applicative.Backwards
import Data.Coerce
import Data.Functor.Compose
import Data.Functor.Product
import Data.Functor.Reverse
import Data.Functor.Sum
import Data.GADT.Compare
import Data.HKD.Classes
import Data.Kind
import Data.Proxy
import Data.Function.Coerce
import Data.Type.Equality
import GHC.Generics
import qualified Data.Monoid as Monoid

-------------------------------------------------------------------------------
-- FContravariant
-------------------------------------------------------------------------------

class FContravariant (t :: (k -> Type) -> Type) where
  fcontramap :: (f ~> g) -> t g -> t f
  default fcontramap :: (Generic1 t, FContravariant (Rep1 t)) => (f ~> g) -> t g -> t f
  fcontramap f = to1 . fcontramap f . from1
  {-# inline fcontramap #-}

instance FContravariant Proxy where
  fcontramap _ Proxy = Proxy
  {-# inline fcontramap #-}

instance FContravariant (Const a) where
  fcontramap _ (Const a) = Const a
  {-# inline fcontramap #-}

instance (Functor f, FContravariant g) => FContravariant (Compose f g) where
  fcontramap f = Compose #. fmap (fcontramap f) .# getCompose
  {-# inline fcontramap #-}

instance (FContravariant f, FContravariant g) => FContravariant (Product f g) where
  fcontramap f (Pair g h) = Pair (fcontramap f g) (fcontramap f h)
  {-# inline fcontramap #-}

instance (FContravariant f, FContravariant g) => FContravariant (Sum f g) where
  fcontramap f (InL g) = InL (fcontramap f g)
  fcontramap f (InR h) = InR (fcontramap f h)
  {-# inline fcontramap #-}

instance FContravariant (K1 i a) where
  fcontramap _ = coerce
  {-# inline fcontramap #-}

deriving newtype instance FContravariant f => FContravariant (M1 i c f)
deriving newtype instance FContravariant f => FContravariant (Rec1 f)

instance FContravariant U1 where
  fcontramap _ U1 = U1
  {-# inline fcontramap #-}

instance FContravariant V1 where
  fcontramap _ = \case
  {-# inline fcontramap #-}

instance (Functor f, FContravariant g) => FContravariant (f :.: g) where
  fcontramap f = Comp1 #. fmap (fcontramap f) .# unComp1
  {-# inline fcontramap #-}

instance (FContravariant f, FContravariant g) => FContravariant (f :*: g) where
  fcontramap f (g :*: h) = fcontramap f g :*: fcontramap f h
  {-# inline fcontramap #-}

instance (FContravariant f, FContravariant g) => FContravariant (f :+: g) where
  fcontramap f (L1 g) = L1 (fcontramap f g)
  fcontramap f (R1 h) = R1 (fcontramap f h)
  {-# inline fcontramap #-}

deriving newtype instance FContravariant f => FContravariant (Backwards f)
deriving newtype instance FContravariant f => FContravariant (Reverse f)
deriving newtype instance FContravariant f => FContravariant (Monoid.Alt f)
deriving newtype instance FContravariant f => FContravariant (Monoid.Ap f)

newtype FEquivalence a = FEquivalence
  { getFEquivalence :: forall x y. a x -> a y -> Maybe (x :~: y)
  }

instance FContravariant FEquivalence where
  fcontramap f (FEquivalence g) = FEquivalence \i j -> g (f i) (f j)
  {-# inline fcontramap #-}

newtype FComparison a = FComparison
  { getFComparison :: forall x y. a x -> a y -> GOrdering x y
  }

instance FContravariant FComparison where
  fcontramap f (FComparison g) = FComparison \i j -> g (f i) (f j)
  {-# inline fcontramap #-}

newtype FOp b f = FOp { getFOp :: forall x. f x -> b }

instance FContravariant (FOp b) where
  fcontramap f (FOp g) = FOp (g . f)
  {-# inline fcontramap #-}

class FContravariant f => FSemidivisible f where
  fdivide  :: (a ~> b :*: c) -> f b -> f c -> f a

class FSemidivisible f => FDivisible f where
  fconquer :: f a

fdivided :: FSemidivisible f => f a -> f b -> f (a :*: b)
fdivided = fdivide id
{-# inline fdivided #-}

fconquered :: FDivisible f => f U1
fconquered = fconquer
{-# inline fconquered #-}

fliftDiv :: FDivisible f => (a ~> b) -> f b -> f a
fliftDiv f = fdivide ((:*:) U1 . f) fconquer
{-# inline fliftDiv #-}

class FSemidivisible f => FSemidecidable f where
  fchoose :: (a ~> (b :+: c)) -> f b -> f c -> f a
  flose :: (a ~> V1) -> f a

class (FDivisible f, FSemidecidable f) => FDecidable f
instance (FDivisible f, FSemidecidable f) => FDecidable f

flost :: FDecidable f => f V1
flost = flose id
{-# inline flost #-}

fchosen :: FSemidecidable f => f a -> f b -> f (a :+: b)
fchosen = fchoose id
{-# inline fchosen #-}

-- * FDivisible Instances
--
-- FEquivalence a = (forall x y. a x -> a y -> Maybe (x :~: y)

instance FSemidivisible FEquivalence where
  fdivide f g h = FEquivalence $ \a a' -> case f a of
    b :*: c -> case f a' of
      b' :*: c' -> getFEquivalence g b b' *> getFEquivalence h c c'
  {-# inline fdivide #-}

instance FSemidecidable FEquivalence where
  fchoose f g h = FEquivalence $ \a a' -> case f a of
    L1 b -> case f a' of
      L1 b' -> getFEquivalence g b b'
      _ -> Nothing
    R1 c -> case f a' of
      R1 c' -> getFEquivalence h c c'
      _ -> Nothing
  {-# inline fchoose #-}

  flose f = FEquivalence $ \a -> case f a of
  {-# inline flose #-}

instance FSemidivisible FComparison where
  fdivide = \f g h -> FComparison $ \a a' -> case f a of
    b :*: c -> case f a' of
      b' :*: c' -> case getFComparison g b b' of
        GLT -> GLT
        GEQ -> getFComparison h c c'
        GGT -> GGT
  {-# inline fdivide #-}

instance FSemidecidable FComparison where
  fchoose = \f g h -> FComparison $ \a a' -> case f a of
    L1 b -> case f a' of
      L1 b' -> getFComparison g b b'
      _ -> GLT
    R1 c -> case f a' of
      R1 c' -> getFComparison h c c'
      _ -> GGT
  {-# inline fchoose #-}

  flose = \f -> FComparison $ \a -> case f a of
  {-# inline flose #-}

instance Semigroup b => FSemidivisible (FOp b) where
  fdivide = \f g h -> FOp $ \x -> case f x of
    b :*: c -> getFOp g b <> getFOp h c
  {-# inline fdivide #-}

instance Monoid b => FDivisible (FOp b) where
  fconquer = FOp $ \_ -> mempty
  {-# inline fconquer #-}

instance Semigroup c => FSemidivisible (K1 i c) where
  fdivide = \_ (K1 m) (K1 n) -> K1 (m <> n)
  {-# inline fdivide #-}

instance Monoid c => FDivisible (K1 i c) where
  fconquer = K1 mempty
  {-# inline fconquer #-}

instance FSemidivisible U1 where
  fdivide = \_ U1 -> coerce
  {-# inline fdivide #-}

instance FDivisible U1 where
  fconquer = U1
  {-# inline fconquer #-}

instance FSemidivisible f => FSemidivisible (Rec1 f) where
  fdivide = \f l -> Rec1 #. fdivide f (unRec1 l) .# unRec1
  {-# inline fdivide #-}

instance FDivisible f => FDivisible (Rec1 f) where
  fconquer = Rec1 fconquer
  {-# inline fconquer #-}

instance FSemidivisible f => FSemidivisible (M1 i c f) where
  fdivide = \f (M1 l) -> M1 #. fdivide f l .# unM1
  {-# inline fdivide #-}

instance FDivisible f => FDivisible (M1 i c f) where
  fconquer = M1 fconquer
  {-# inline fconquer #-}

instance (FSemidivisible f, FSemidivisible g) => FSemidivisible (f :*: g) where
  fdivide = \f (l1 :*: r1) (l2 :*: r2) -> fdivide f l1 l2 :*: fdivide f r1 r2
  {-# inline fdivide #-}

instance (FDivisible f, FDivisible g) => FDivisible (f :*: g) where
  fconquer = fconquer :*: fconquer
  {-# inline fconquer #-}

-- | only needs Semiapplicative
instance (Applicative f, FSemidivisible g) => FSemidivisible (f :.: g) where
  fdivide = \f (Comp1 l) (Comp1 r) -> Comp1 (liftA2 (fdivide f) l r)
  {-# inline fdivide #-}

instance (Applicative f, FDivisible g) => FDivisible (f :.: g) where
  fconquer = Comp1 $ pure fconquer
  {-# inline fconquer #-}

-- * FDecidable

instance Semigroup b => FSemidecidable (FOp b) where
  fchoose = \ f g h -> FOp $ \x -> case f x of
    L1 b -> getFOp g b
    R1 b -> getFOp h b
  {-# inline fchoose #-}

  flose = \f -> FOp (\x -> case f x of)
  {-# inline flose #-}

instance FSemidecidable U1 where
  fchoose = \_ U1 -> coerce
  {-# inline fchoose #-}

  flose = \_ -> U1
  {-# inline flose #-}

instance FSemidecidable f => FSemidecidable (Rec1 f) where
  fchoose = \f l -> Rec1 #. fchoose f (unRec1 l) .# unRec1
  {-# inline fchoose #-}

  flose = \f -> Rec1 $ flose f
  {-# inline flose #-}

instance FSemidecidable f => FSemidecidable (M1 i c f) where
  fchoose = \f l -> M1 #. fchoose f (unM1 l) .# unM1
  {-# inline fchoose #-}

  flose = \f -> M1 $ flose f
  {-# inline flose #-}

instance (FSemidecidable f, FSemidecidable g) => FSemidecidable (f :*: g) where
  fchoose = \f (l1 :*: r1) (l2 :*: r2) -> fchoose f l1 l2 :*: fchoose f r1 r2
  {-# inline fchoose #-}

  flose = \f -> flose f :*: flose f
  {-# inline flose #-}

-- | only needs Semiapplicative
instance (Applicative f, FSemidecidable g) => FSemidecidable (f :.: g) where
  fchoose = \f l -> Comp1 #. liftA2 (fchoose f) (unComp1 l) .# unComp1
  {-# inline fchoose #-}

  flose = \x -> Comp1 $ pure $ flose x
  {-# inline flose #-}

class FSemideciding q t where
  fsemideciding
    :: FSemidecidable f
    => (s ~> t)
    -> (forall b. q b => f b)
    -> f s
  default fsemideciding
    :: (Generic1 t, FSemideciding q (Rep1 t), FSemidecidable f)
    => (s ~> t)
    -> (forall b. q b => f b)
    -> f s
  fsemideciding = \ st -> fsemideciding @q (from1 . st)
  {-# inline fsemideciding #-}

instance (FSemideciding q s, FSemideciding q t) => FSemideciding q (Product s t)
instance (FSemideciding q s, FSemideciding q t) => FSemideciding q (Sum s t)
deriving newtype instance FSemideciding q f => FSemideciding q (Monoid.Alt f)
deriving newtype instance FSemideciding q f => FSemideciding q (Monoid.Ap f)
-- deriving newtype instance FSemideciding q f => FSemideciding q (Backwards f)
-- deriving newtype instance FSemideciding q f => FSemideciding q (Reverse f)

instance (FSemideciding q s, FSemideciding q t) => FSemideciding q (s :*: t) where
  fsemideciding = \k f -> fdivide k (fsemideciding @q id f) (fsemideciding @q id f)

instance (FSemideciding q s, FSemideciding q t) => FSemideciding q (s :+: t) where
  fsemideciding = \k f -> fchoose k (fsemideciding @q id f) (fsemideciding @q id f)

instance FSemideciding q V1 where
  fsemideciding = \k _ -> flose $ \x -> case k x of

instance FSemideciding q f => FSemideciding q (M1 i c f) where
  fsemideciding = \k f -> fsemideciding @q (M1 #. k) f

-- instance q f => FSemideciding q (Rec1 f) where
--  fsemideciding k f = fcontramap (unRec1 #. k) f

instance FSemideciding q f => FSemideciding q (Rec1 f) where
  fsemideciding = \k f -> fsemideciding @q (unRec1 #. k) f

instance q (Const c) => FSemideciding q (K1 i c) where
  fsemideciding k f = fcontramap ((Const . unK1) #. k) f

--class FSemideciding q t => FDeciding q t where
--  fdeciding :: FSemidecidable f => p q -> (forall b. q b => f b) -> f (t a)
