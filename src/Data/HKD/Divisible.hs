{-# Language RankNTypes #-}
{-# Language PolyKinds #-}
{-# Language DataKinds #-}
{-# Language Safe #-}
{-# Language TypeOperators #-}

module Data.HKD.Divisible
( FDivisible(..)
, fdivided
, fconquered
, fliftDiv
, FDecidable(..)
, flost
, fchosen
) where

import GHC.Generics
import Data.HKD
import Data.Kind

class FContravariant f => FDivisible (f :: (i -> Type) -> Type) where
  fdivide  :: (a ~> b :*: c) -> f b -> f c -> f a
  fconquer :: f a

fdivided :: FDivisible f => f a -> f b -> f (a :*: b)
fdivided = fdivide id
{-# inline fdivided #-}

fconquered :: FDivisible f => f U1
fconquered = fconquer
{-# inline fconquered #-}

fliftDiv :: FDivisible f => (a ~> b) -> f b -> f a

fliftDiv f = fdivide ((:*:) U1 . f) fconquer
{-# inline fliftDiv #-}

class FDivisible f => FDecidable f where
  flose :: (a ~> V1) -> f a
  fchoose :: (a ~> (b :+: c)) -> f b -> f c -> f a

flost :: FDecidable f => f V1
flost = flose id
{-# inline flost #-}

fchosen :: FDecidable f => f a -> f b -> f (a :+: b)
fchosen = fchoose id
{-# inline fchosen #-}

-- * FDivisible Instances

instance Monoid c => FDivisible (K1 i c) where
  fdivide _ (K1 m) (K1 n) = K1 (mappend m n)
  fconquer = K1 mempty
  {-# inline fdivide #-}
  {-# inline fconquer #-}

instance FDivisible U1 where
  fdivide _ U1 U1 = U1
  fconquer = U1
  {-# inline fdivide #-}
  {-# inline fconquer #-}

instance FDivisible f => FDivisible (Rec1 f) where
  fdivide f (Rec1 l) (Rec1 r) = Rec1 $ fdivide f l r
  fconquer = Rec1 fconquer
  {-# inline fdivide #-}
  {-# inline fconquer #-}

instance FDivisible f => FDivisible (M1 i c f) where
  fdivide f (M1 l) (M1 r) = M1 $ fdivide f l r
  fconquer = M1 fconquer
  {-# inline fdivide #-}
  {-# inline fconquer #-}

instance (FDivisible f, FDivisible g) => FDivisible (f :*: g) where
  fdivide f (l1 :*: r1) (l2 :*: r2) = fdivide f l1 l2 :*: fdivide f r1 r2
  fconquer = fconquer :*: fconquer
  {-# inline fdivide #-}
  {-# inline fconquer #-}

instance (Applicative f, FDivisible g) => FDivisible (f :.: g) where
  fdivide f (Comp1 l) (Comp1 r) = Comp1 (fdivide f <$> l <*> r)
  fconquer = Comp1 $ pure fconquer
  {-# inline fdivide #-}
  {-# inline fconquer #-}

-- * FDecidable

instance FDecidable U1 where
  flose _ = U1
  fchoose _ U1 U1 = U1
  {-# inline flose #-}
  {-# inline fchoose #-}

instance FDecidable f => FDecidable (Rec1 f) where
  flose f = Rec1 $ flose f
  fchoose f (Rec1 l) (Rec1 r) = Rec1 $ fchoose f l r
  {-# inline flose #-}
  {-# inline fchoose #-}

instance FDecidable f => FDecidable (M1 i c f) where
  flose f = M1 $ flose f
  fchoose f (M1 l) (M1 r) = M1 $ fchoose f l r
  {-# inline flose #-}
  {-# inline fchoose #-}

instance (FDecidable f, FDecidable g) => FDecidable (f :*: g) where
  flose f = flose f :*: flose f
  fchoose f (l1 :*: r1) (l2 :*: r2) = fchoose f l1 l2 :*: fchoose f r1 r2
  {-# inline flose #-}
  {-# inline fchoose #-}

instance (Applicative f, FDecidable g) => FDecidable (f :.: g) where
  flose x = Comp1 $ pure $ flose x
  fchoose f (Comp1 l) (Comp1 r) = Comp1 (fchoose f <$> l <*> r)
  {-# inline flose #-}
  {-# inline fchoose #-}
