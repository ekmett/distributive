{-# Language CPP #-}
{-# Language AllowAmbiguousTypes #-}
{-# Language ConstraintKinds #-}
{-# Language DataKinds #-}
{-# Language DefaultSignatures #-}
{-# Language EmptyCase #-}
{-# Language FlexibleContexts #-}
{-# Language FlexibleInstances #-}
{-# Language GADTs #-}
{-# Language InstanceSigs #-}
{-# Language MultiParamTypeClasses #-}
{-# Language PolyKinds #-}
{-# Language RankNTypes #-}
{-# Language ScopedTypeVariables #-}
{-# Language Trustworthy #-}
{-# Language TypeApplications #-}
{-# Language TypeOperators #-}
{-# Language StandaloneDeriving #-}
{-# Language DerivingStrategies #-}
{-# Language GeneralizedNewtypeDeriving #-}

#ifndef MIN_VERSION_base
#define MIN_VERSION_base(_x,_y,_z) 1
#endif

module Data.HKD.Contravariant.Divisible
( FSemidivisible(..)
, FDivisible(..)
, fdivided
, fconquered
, fliftDiv
, FSemidecidable(..)
, FDecidable
, flost
, fchosen
--, FDeciding(..)
, FSemideciding(..)
) where

import Control.Applicative
import Data.Coerce
import Data.Distributive.Internal.Coerce
import Data.Distributive.Internal.Orphans ()
import Data.Functor.Product
import Data.Functor.Sum
import qualified Data.Monoid as Monoid
import Data.GADT.Compare
import Data.HKD
import Data.HKD.Contravariant
-- import Data.Semigroup
import GHC.Generics

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
  fsemideciding = \ _ _ -> undefined

instance (FSemideciding q s, FSemideciding q t) => FSemideciding q (Product s t)
instance (FSemideciding q s, FSemideciding q t) => FSemideciding q (Sum s t)
deriving newtype instance FSemideciding q f => FSemideciding q (Monoid.Alt f)
#if MIN_VERSION_base(4,12,0)
deriving newtype instance FSemideciding q f => FSemideciding q (Monoid.Ap f)
#endif
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
