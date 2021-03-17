{-# Language CPP #-}
{-# Language AllowAmbiguousTypes #-}
{-# Language DataKinds #-}
{-# Language DeriveTraversable #-}
{-# Language DerivingStrategies #-}
{-# Language DerivingVia #-}
{-# Language GADTs #-}
{-# Language GeneralizedNewtypeDeriving #-}
{-# Language InstanceSigs #-}
{-# Language KindSignatures #-}
{-# Language BangPatterns #-}
{-# Language MagicHash #-}
{-# Language MultiParamTypeClasses #-}
{-# Language FunctionalDependencies #-}
{-# Language PatternSynonyms #-}
{-# Language PolyKinds #-}
{-# Language RankNTypes #-}
{-# Language RoleAnnotations #-}
{-# Language ScopedTypeVariables #-}
{-# Language StandaloneDeriving #-}
{-# Language FlexibleInstances #-}
{-# Language TypeApplications #-}
{-# Language TypeFamilies #-}
{-# Language TypeOperators #-}
{-# Language UnboxedTuples #-}
{-# Language Unsafe #-}
{-# Language ViewPatterns #-}
{-# options_haddock hide #-}

module Data.Distributive.Internal.Vec
( Vec(UnsafeVec,Vec,toVector)
, pattern V
, FromVector(..)
, withDim
) where

import Control.Monad
import Control.Monad.Reader.Class
import Control.Monad.Fix
import Control.Monad.Zip
import Data.Distributive
import Data.Distributive.Internal.Coerce
import Data.Distributive.Internal.Fin
import Data.Foldable.WithIndex
import Data.Functor.Classes
import Data.Functor.Identity
import Data.Functor.WithIndex
import Data.HKD
import Data.Proxy
import Data.Traversable.WithIndex
import Data.Type.Equality
import Data.Vector as V
import GHC.Exts
import GHC.TypeNats
import Unsafe.Coerce
import Text.Read

type role Vec nominal representational
newtype Vec (n :: Nat) a = UnsafeVec (Vector a)
  deriving stock (Functor, Foldable, Traversable)
  deriving newtype (Eq, Eq1, Ord, Ord1, Show, Show1)

pattern Vec :: Vector a -> Vec n a
pattern Vec { toVector } <- UnsafeVec toVector

{-# complete Vec :: Vec #-}

instance KnownNat n => Distributive (Vec n) where
  type Log (Vec n) = Fin n
  scatter = \(k :: w Identity -> r) f (ffmap f -> w) -> UnsafeVec $
    generate (int @n) $ \i -> k $ ffmap (\v -> Identity $ index v $ UnsafeFin i) w
  {-# inlinable scatter #-}

  tabulate = \(f :: Fin n -> a) -> UnsafeVec $ generate (int @n) (f .# UnsafeFin)
  {-# inlinable tabulate #-}

  index :: forall a. Vec n a -> Fin n -> a
  index = coerce ((!) :: Vector a -> Int -> a)
  {-# inline index #-}

instance (KnownNat n, Read a) => Read (Vec n a) where
  readPrec = do
    l <- step readPrec 
    let v = V.fromList l
    UnsafeVec v <$ guard (V.length v == int @n)

instance KnownNat n => Read1 (Vec n) where
  liftReadPrec _ rl = do
    l <- rl
    let v = V.fromList l
    UnsafeVec v <$ guard (V.length v == int @n)
  {-# inline liftReadPrec #-}

instance FunctorWithIndex (Fin n) (Vec n) where
  imap :: forall a b. (Fin n -> a -> b) -> Vec n a -> Vec n b
  imap = coerce (V.imap :: (Int -> a -> b) -> Vector a -> Vector b)
  {-# inline imap #-}

instance FoldableWithIndex (Fin n) (Vec n) where
  ifoldMap f = V.ifoldr (\i a b -> f (UnsafeFin i) a `mappend` b) mempty .# toVector
  {-# inline ifoldMap #-}

instance TraversableWithIndex (Fin n) (Vec n) where
  itraverse f (toVector -> as) = (UnsafeVec #. V.fromListN (V.length as)) <$>
    itraverse (f .# UnsafeFin) (V.toList as)
  {-# inline itraverse #-}

data SomeVec a where
  SomeVec :: KnownNat n => Vec n a -> SomeVec a

asVec :: FromVector t a => t -> SomeVec a
asVec ((UnsafeVec . asVector) -> v) = withDim v (SomeVec v)
{-# inline asVec #-}

withDim :: forall n a r. Vec n a -> (KnownNat n => r) -> r
withDim v r = case someNatVal (fromIntegral $ V.length (toVector v)) of
  SomeNat (Proxy :: Proxy n') -> case unsafeCoerce Refl of
    (Refl :: n :~: n') -> r
{-# inline withDim #-}

class FromVector t a | t -> a where
  asVector :: t -> Vector a
  vectorAs :: Vector a -> t

instance FromVector (Vector a) a where
  asVector = id
  vectorAs = id

instance FromVector [a] a where
  asVector = V.fromList
  vectorAs = V.toList

pattern V :: FromVector t a => KnownNat n => Vec n a -> t
pattern V v <- (asVec -> SomeVec v) where
  V v = vectorAs (toVector v)

{-# complete V :: Vector #-}
{-# complete V :: [] #-}

#if __GLASGOW_HASKELL__ >= 806

deriving via Dist (Vec n) instance KnownNat n => Applicative (Vec n)
deriving via Dist (Vec n) instance KnownNat n => Monad (Vec n)
deriving via Dist (Vec n) instance KnownNat n => MonadFix (Vec n)
deriving via Dist (Vec n) instance KnownNat n => MonadZip (Vec n)
deriving via Dist (Vec n) instance KnownNat n => MonadReader (Fin n) (Vec n)
deriving via Dist (Vec n) a instance (KnownNat n, Num a) => Num (Vec n a)
deriving via Dist (Vec n) a instance (KnownNat n, Fractional a) => Fractional (Vec n a)
deriving via Dist (Vec n) a instance (KnownNat n, Floating a) => Floating (Vec n a)

#else

instance KnownNat n => Applicative (Vec n) where
  pure = pureDist
  liftA2 = liftD2
  (<*>) = apDist
  _ *> n = n
  (<*) = const

instance KnownNat n => Monad (Vec n) where
  (>>=) = bindDist
  (>>) = (*>)

instance KnownNat n => MonadFix (Vec n) where
  mfix = mfixDist

instance KnownNat n => MonadZip (Vec n) where
  mzipWith = mzipWithDist

instance KnownNat n => MonadReader (Fin n) (Vec n) where
  ask = askDist
  local = localDist
  reader = tabulate

instance (KnownNat n, Num a) => Num (Vec n a) where
  (+) = liftA2 (+)
  (-) = liftA2 (-)
  (*) = liftA2 (*)
  negate = fmap negate
  abs = fmap abs
  signum = fmap signum
  fromInteger = pure . fromInteger

instance (KnownNat n, Fractional b) => Fractional (Vec n a) where
  (/) = liftA2 (/)
  recip = fmap recip
  fromRational = pure . fromRational

instance (KnownNat n, Floating b) => Floating (Vec n a) where
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

#endif
