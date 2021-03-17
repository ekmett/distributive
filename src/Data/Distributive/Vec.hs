{-# Language CPP #-}
{-# Language AllowAmbiguousTypes #-}
{-# Language DataKinds #-}
{-# Language DerivingStrategies #-}
{-# Language DerivingVia #-}
{-# Language GADTs #-}
{-# Language KindSignatures #-}
{-# Language BangPatterns #-}
{-# Language MagicHash #-}
{-# Language MultiParamTypeClasses #-}
{-# Language PatternSynonyms #-}
{-# Language PolyKinds #-}
{-# Language RankNTypes #-}
{-# Language ScopedTypeVariables #-}
{-# Language StandaloneDeriving #-}
{-# Language Trustworthy #-}
{-# Language TypeApplications #-}
{-# Language TypeFamilies #-}
{-# Language TypeOperators #-}
{-# Language UnboxedTuples #-}
{-# Language ViewPatterns #-}

module Data.Distributive.Vec
( Fin(Fin,Fin#,FZ,FS)
, toFin
, Vec(Vec,Vec#,toArray)
, pattern ArrayVec
, pattern ListVec
, withDim
-- UnsafeVec, UnsafeVec#
-- UnsafeFin, UnsafeFin#
) where

import Control.Monad
import Control.Monad.Reader.Class
import Control.Monad.Fix
import Control.Monad.Zip
import Data.Distributive
import Data.Distributive.Coerce
import Data.Foldable
import Data.Foldable.WithIndex
import Data.Functor.Classes
import Data.Functor.Identity
import Data.Functor.WithIndex
import Data.GADT.Compare
import Data.HKD
import Data.Primitive.Array
import Data.Proxy
import Data.Traversable.WithIndex
import Data.Type.Coercion
import Data.Type.Equality
import GHC.Exts
import GHC.ST
import GHC.TypeNats
import Unsafe.Coerce
import Text.Read

type S n = 1 + n

newtype Fin (n :: Nat) = UnsafeFin { fromFin :: Int }
  deriving (Eq, Ord)

instance Show (Fin n) where
  showsPrec d (UnsafeFin n) = showsPrec d n

instance KnownNat n => Read (Fin n) where
  readPrec = do
    i <- readPrec
    UnsafeFin i <$ guard (i < int @n)

pattern UnsafeFin# :: Int# -> Fin n
pattern UnsafeFin# i = UnsafeFin (I# i)
{-# complete UnsafeFin# :: Fin #-}

pattern Fin# :: Int# -> Fin n
pattern Fin# i <- UnsafeFin# i
{-# complete Fin# :: Fin #-}

instance GEq Fin where
  geq (UnsafeFin x) (UnsafeFin y)
    | x == y = Just (unsafeCoerce Refl)
    | otherwise = Nothing
  {-# inline geq #-}

instance GCompare Fin where
  gcompare (UnsafeFin x) (UnsafeFin y) = case compare x y of
    LT -> GLT
    EQ -> unsafeCoerce GEQ
    GT -> GGT
  {-# inline gcompare #-}

instance TestEquality Fin where
  testEquality = geq

instance TestCoercion Fin where
  testCoercion a b = repr <$> geq a b

pattern Fin :: Int -> Fin n
pattern Fin n <- UnsafeFin n

toFin :: forall n. KnownNat n => Int -> Maybe (Fin n)
toFin i
  | i < int @n = Just (UnsafeFin i)
  | otherwise  = Nothing

{-# complete Fin #-}

data Fin' (n :: Nat) where
  FZ' :: Fin' (S n)
  FS' :: Fin n -> Fin' (S n)

upFin :: Fin n -> Fin' n
upFin (UnsafeFin 0) = unsafeCoerce FZ'
upFin (UnsafeFin n) = unsafeCoerce $ FS' $ UnsafeFin (n-1)

pattern FZ :: () => forall m. (n ~ S m) => Fin n
pattern FZ <- (upFin -> FZ') where
  FZ = UnsafeFin 0

pattern FS :: () => forall m. (n ~ S m) => Fin m -> Fin n
pattern FS n <- (upFin -> FS' n) where
  FS n = UnsafeFin (fromFin n - 1)

{-# complete FZ, FS :: Fin #-}

newtype Vec (n :: Nat) a = UnsafeVec (Array a)

pattern UnsafeVec# :: Array# a -> Vec n a
pattern UnsafeVec# x = UnsafeVec (Array x)
{-# complete UnsafeVec# :: Vec #-}

pattern Vec# :: Array# a -> Vec n a
pattern Vec# x <- UnsafeVec# x
{-# complete Vec# :: Vec #-}

-- pattern Vec :: () => KnownLength n => Array# a -> Vec n a

pattern Vec :: Array a -> Vec n a
pattern Vec { toArray } <- UnsafeVec toArray

{-# complete Vec :: Vec #-}

bad :: a
bad = error "uninitialized Vec n entry"

instance KnownNat n => Distributive (Vec n) where
  type Log (Vec n) = Fin n
  scatter (k :: w Identity -> r) f (ffmap f -> w) = runST $ ST $ \s -> case newArray# n# bad s of
    (# s', ma #) -> case go ma n# s' of
      s'' -> case unsafeFreezeArray# ma s'' of
        (# s''', arr #) -> (# s''', UnsafeVec# arr #)
    where
      !(I# n#) = fromIntegral (natVal' (proxy# @n))
      go :: MutableArray# s r -> Int# -> State# s -> State# s
      go _ 0# s = s
      go ma i s = case i -# 1# of
        i' -> case writeArray# ma i' (k $ ffmap (\v -> Identity $ index v $ UnsafeFin $ I# i') w) s of
          s' -> go ma i' s'
  {-# inlinable scatter #-}

  tabulate (f :: Fin n -> a) = runST $ ST $ \s -> case newArray# n# bad s of
    (# s', ma #) -> case go ma n# s' of
      s'' -> case unsafeFreezeArray# ma s'' of
        (# s''', arr #) -> (# s''', UnsafeVec# arr #)
    where
      !(I# n#) = fromIntegral (natVal' (proxy# @n))
      go :: MutableArray# s a -> Int# -> State# s -> State# s
      go _ 0# s = s
      go ma i s = case i -# 1# of
        i' -> case writeArray# ma i' (f $ UnsafeFin (I# i')) s of
          s' -> go ma i' s'
  {-# inlinable tabulate #-}

  index = \(Vec# as) (Fin (I# i)) -> case indexArray# as i of
    (# a #) -> a
  {-# inline index #-}


instance Eq a => Eq (Vec n a) where
  Vec# as == Vec# bs = go (sizeofArray# as) where
    go :: Int# -> Bool
    go 0# = True
    go i = case i -# 1# of
      i' -> case indexArray# as i' of
       (# a #) -> case indexArray# bs i' of
         (# b #) -> if a /= b then False else go i'
  {-# inlinable (==) #-}

instance Ord a => Ord (Vec n a) where
  compare (Vec# as) (Vec# bs) = go 0# (sizeofArray# as) where
    go :: Int# -> Int# -> Ordering
    go i j
      | isTrue# (i ==# j) = EQ
      | otherwise = case indexArray# as i of
        (# a #) -> case indexArray# bs i of
          (# b #) -> case compare a b of
            LT -> LT
            EQ -> go (i +# 1#) j
            GT -> GT
  {-# inlinable compare #-}

instance Foldable (Vec n) where
  foldr f (z :: r) (Vec# as) = go 0# (sizeofArray# as) where
    go :: Int# -> Int# -> r
    go i j
      | isTrue# (i ==# j) = z
      | otherwise = case indexArray# as i of
        (# a #) -> f a (go (i +# 1#) j)
  {-# inline foldr #-}
  foldl f (z :: r) (Vec# as) = go (sizeofArray# as) where
    go :: Int# -> r
    go 0# = z
    go i = case i -# 1# of
      i' -> case indexArray# as i' of
        (# a #) -> f (go i') a
  {-# inline foldl #-}
  toList = foldr (:) []
  {-# inline toList #-}
  length (Vec# as) = I# (sizeofArray# as)
  {-# inline length #-}
  null (Vec# as) = isTrue# (sizeofArray# as ==# 0#)
  {-# inline null #-}

instance Show a => Show (Vec n a) where
  showsPrec d = showsPrec d . Data.Foldable.toList

int :: forall n. KnownNat n => Int
int = fromIntegral $ natVal' (proxy# @n)

instance (KnownNat n, Read a) => Read (Vec n a) where
  readPrec = unsafeFromListN (int @n) <$> step readPrec

instance Eq1 (Vec n) where
  liftEq f (Vec# as) (Vec# bs) = go (sizeofArray# as) where
    go :: Int# -> Bool
    go 0# = True
    go i = case i -# 1# of
      i' -> case indexArray# as i' of
       (# a #) -> case indexArray# bs i' of
         (# b #) -> if f a b then go i' else False
  {-# inlinable liftEq #-}

instance Ord1 (Vec n) where
  liftCompare f (Vec# as) (Vec# bs) = go 0# (sizeofArray# as) where
    go :: Int# -> Int# -> Ordering
    go i j
      | isTrue# (i ==# j) = EQ
      | otherwise = case indexArray# as i of
        (# a #) -> case indexArray# bs i of
          (# b #) -> case f a b of
            LT -> LT
            EQ -> go (i +# 1#) j
            GT -> GT
  {-# inlinable liftCompare #-}

instance Show1 (Vec n) where
  liftShowsPrec _ l _ = l . Data.Foldable.toList
  {-# inline liftShowsPrec #-}

instance KnownNat n => Read1 (Vec n) where
  liftReadPrec _ l = unsafeFromListN (int @n) <$> l
  {-# inline liftReadPrec #-}

instance Functor (Vec n) where
  fmap (f :: a -> b) (Vec# as) = runST $ ST $ \s ->
    case sizeofArray# as of
      n -> case newArray# n bad s of
        (# s', ma #) -> case go ma n s' of
          s'' -> case unsafeFreezeArray# ma s'' of
            (# s''', arr #) -> (# s''', UnsafeVec# arr #)
    where
    go :: MutableArray# s b -> Int# -> State# s -> State# s
    go _ 0# s = s
    go ma i s = case i -# 1# of
      i' -> case indexArray# as i' of
        (# a #) -> case writeArray# ma i' (f a) s of
          s' -> go ma i' s'
  {-# inline fmap #-}

instance FunctorWithIndex (Fin n) (Vec n) where
  imap (f :: Fin n -> a -> b) (Vec# as) = runST $ ST $ \s ->
    case sizeofArray# as of
      n -> case newArray# n bad s of
        (# s', ma #) -> case go ma n s' of
          s'' -> case unsafeFreezeArray# ma s'' of
            (# s''', arr #) -> (# s''', UnsafeVec# arr #)
    where
    go :: MutableArray# s b -> Int# -> State# s -> State# s
    go _ 0# s = s
    go ma i s = case i -# 1# of
      i' -> case indexArray# as i' of
        (# a #) -> case writeArray# ma i' (f (UnsafeFin# i') a) s of
          s' -> go ma i' s'
  {-# inline imap #-}

instance FoldableWithIndex (Fin n) (Vec n) where
  ifoldMap (f :: Fin n -> a -> m) (Vec# as) = go 0# (sizeofArray# as) where
    go :: Int# -> Int# -> m
    go i j
      | isTrue# (i ==# j) = mempty
      | otherwise = case indexArray# as i of
        (# a #) -> f (UnsafeFin# i) a <> go (i +# 1#) j
  {-# inline ifoldMap #-}
instance Traversable (Vec n) where
  traverse f as = unsafeFromListN (length as) <$> traverse f (Data.Foldable.toList as)
  {-# inline traverse #-}

instance TraversableWithIndex (Fin n) (Vec n) where
  itraverse f as = unsafeFromListN (length as) <$> itraverse (f .# UnsafeFin) (Data.Foldable.toList as)
  {-# inline itraverse #-}

data SomeVec a where
  SomeVec :: KnownNat n => Vec n a -> SomeVec a

fromArray :: Array a -> SomeVec a
fromArray (UnsafeVec -> v) = withDim v (SomeVec v)
{-# inline fromArray #-}

unsafeFromListN :: Int -> [a] -> Vec n a
unsafeFromListN (I# n) as = runST $ ST $ \s -> case newArray# n bad s of
  (# s', ma #) -> case go ma as 0# s' of
    s'' -> case unsafeFreezeArray# ma s'' of
      (# s''', arr #) -> (# s''', UnsafeVec# arr #)
  where
    go :: MutableArray# s a -> [a] -> Int# -> State# s -> State# s
    go _ [] _ s = s
    go ma (x:xs) i s = case writeArray# ma i x s of
      s' -> go ma xs (i +# 1#) s'
{-# inline unsafeFromListN #-}

withDim :: forall n a r. Vec n a -> (KnownNat n => r) -> r
withDim v r = case someNatVal (fromIntegral $ length v) of
  SomeNat (Proxy :: Proxy n') -> case unsafeCoerce Refl of
    (Refl :: n :~: n') -> r
{-# inline withDim #-}

pattern ArrayVec :: () => KnownNat n => Vec n a -> Array a
pattern ArrayVec v <- (fromArray -> SomeVec v) where
  ArrayVec v = toArray v

pattern ListVec :: () => KnownNat n => Vec n a -> [a]
pattern ListVec v <- (fromList -> ArrayVec v) where
  ListVec v = Data.Foldable.toList (toArray v)

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
