{-# Language CPP #-}
{-# Language AllowAmbiguousTypes #-}
{-# Language ConstraintKinds #-}
{-# Language DataKinds #-}
{-# Language DeriveDataTypeable #-}
{-# Language DeriveLift #-}
{-# Language PolyKinds #-}
{-# Language DerivingStrategies #-}
{-# Language FlexibleContexts #-}
{-# Language GADTs #-}
{-# Language KindSignatures #-}
{-# Language MagicHash #-}
{-# Language LambdaCase #-}
{-# Language PatternSynonyms #-}
{-# Language RankNTypes #-}
{-# Language RoleAnnotations #-}
{-# Language ScopedTypeVariables #-}
{-# Language StandaloneDeriving #-}
{-# Language TypeApplications #-}
{-# Language TypeFamilies #-}
{-# Language TypeOperators #-}
{-# Language UndecidableInstances #-}
{-# Language Unsafe #-}
{-# Language ViewPatterns #-}
{-# options_haddock hide #-}

-- |
-- Copyright   : (C) 2021 Edward Kmett,
-- License     : BSD-2-Clause OR Apache-2.0
-- Maintainer  : Edward Kmett <ekmett@gmail.com>
-- Stability   : provisional
-- Portability : non-portable

module Numeric.Fin.Internal
( Fin(UnsafeFin,Fin,FZ,FS,fromFin,KnownFZ,KnownFS)
, pattern IntFin
, toFin
, int
, S
, cataFin
, universe
, mirrorFin
, absurdFin
, boringFin
, isMin
, weakenRight1
, weakenLeft1
, weakenRight
, weakenLeft
, split
, append
#if __GLASGOW_HASKELL__ >= 810
, validFin
#endif
) where

import Control.Monad
import Data.Coerce
import Data.Data
import Data.GADT.Show
import GHC.Arr
import GHC.Exts
import GHC.TypeNats
import GHC.TypeLits (TypeError, ErrorMessage(..))
import Language.Haskell.TH.Syntax hiding (Type)
import Text.Read
import Unsafe.Coerce


-- $setup
-- >>> :set -XTypeApplications -XDataKinds -XScopedTypeVariables -XTemplateHaskell

-- | Turn a KnownNat into an Int. Use with @TypeApplications@.
--
-- >>> int @5
-- 5
int :: forall (n :: Nat). KnownNat n => Int
int = fromIntegral $ natVal' (proxy# :: Proxy# n)

-- | The successor of a natural number.
type S n = 1 + n

-- | @'Fin' n@ is a natural number < @n@.
-- In practice, we limit ourselves by encoding it as an 'Int'
-- as it unboxes better, and most of the time you take it out
-- you are immediately going to convert it to such. If you really
-- need a bigger a 'Fin', you'll need to roll your own.
type role Fin nominal
newtype Fin (n :: Nat)
  -- | This is more unsafe than it looks.
  = UnsafeFin
  { fromFin :: Int
  }
  deriving stock (Eq, Ord, Ix)

-- | >>> $$(liftTyped (FS FZ :: Fin 4))
-- 1
deriving stock instance Lift (Fin n)

instance (KnownNat n, Typeable n) => Data (Fin n) where
  toConstr (Fin 0) = finZConstr
  toConstr (Fin _) = finSConstr
  dataTypeOf _ = case int @n of
    0 -> finEmptyDataType
    _ -> finDataType
  gfoldl _ z KnownFZ = z KnownFZ
  gfoldl k z (KnownFS n) = z KnownFS `k` n
  gunfold k z c = case natVal (Proxy :: Proxy n) of
    0 -> error "gunfold: Fin 0"
    n -> case constrIndex c of
      1 -> z (UnsafeFin 0)
      2 -> case someNatVal $ n - 1 of
        SomeNat (Proxy :: Proxy m) -> case unsafeCoerce Refl of
          (Refl :: n :~: S m) -> k (z KnownFS)
      _ -> error "gunfold: Fin: unknown constructor"

finZConstr, finSConstr :: Constr
finZConstr = mkConstr finDataType "FZ" [] Data.Data.Prefix
finSConstr = mkConstr finDataType "FS" [] Data.Data.Prefix
{-# noinline finZConstr #-}
{-# noinline finSConstr #-}

finDataType :: DataType
finDataType = mkDataType "Numeric.Fin.Fin" [finZConstr, finSConstr]
{-# noinline finDataType #-}

finEmptyDataType :: DataType
finEmptyDataType = mkDataType "Numeric.Fin.Fin" []
{-# noinline finEmptyDataType #-}

type family NonZero (p :: ErrorMessage) (n :: Nat) :: Constraint where
  NonZero p 0 = TypeError p
  NonZero _ _ = ()

instance (NonZero ('Text "Bounded: Fin 0 is uninhabited") n, KnownNat n) => Bounded (Fin n) where
  minBound = UnsafeFin 0
  maxBound = UnsafeFin (int @n - 1)
  {-# inline minBound #-}
  {-# inline maxBound #-}

instance (NonZero ('Text "Enum: Fin 0 is uninhabited") n, KnownNat n) => Enum (Fin n) where
  succ (Fin i)
    | i < int @n - 1 = UnsafeFin (i + 1)
    | otherwise = error "Fin.succ: too big"
  pred (Fin 0) = error "Fin.pred: too small"
  pred (Fin n) = UnsafeFin (n - 1)
  fromEnum = fromFin
  toEnum x
    | x < 0 = error "Fin.toEnum: too small"
    | x >= int @n = error "Fin.toEnum: too big"
    | otherwise = UnsafeFin x
  enumFrom = coerce $ enumFrom @Int
  enumFromTo = coerce (enumFromTo @Int)
  enumFromThen (Fin i) (Fin j)
    | i <= j = coerce $ enumFromThenTo i j (int @n)
    | otherwise = coerce $ enumFromThenTo i j 0
  enumFromThenTo = coerce (enumFromThenTo @Int)

instance GShow Fin where
  gshowsPrec = showsPrec
  {-# inline gshowsPrec #-}

instance Show (Fin n) where
  showsPrec = coerce (showsPrec :: Int -> Int -> String -> String)
  {-# inline showsPrec #-}

instance KnownNat n => Read (Fin n) where
  readPrec = do
    i <- readPrec
    UnsafeFin i <$ guard (i < int @n)
  {-# inline readPrec #-}

-- | You can pattern match on a Fin with this constructor,
-- but not construct. If you really truly want need to
-- construct a 'Fin' using an unsafe naked 'Int' and you
-- pinky-swear that you are going to do it correctly,
-- look at 'UnsafeFin', you animal.
--
-- >>> case FS FZ of Fin n -> n
-- 1
pattern Fin :: Int -> Fin n
pattern Fin n <- UnsafeFin n
{-# complete Fin #-}

-- | You can construct a Fin safely this way.
--
-- >>> toFin 2 :: Maybe (Fin 4)
-- Just 2
--
-- >>> toFin 2 :: Maybe (Fin 2)
-- Nothing
toFin :: forall n. KnownNat n => Int -> Maybe (Fin n)
toFin i
  | 0 <= i && i < int @n = Just (UnsafeFin i)
  | otherwise  = Nothing
{-# inline toFin #-}

-- | This is a pattern on 'Int' that can be used to
-- safely construct a Fin. Pattern match fails
-- if the 'Int' of out of bounds.
--
-- >>> case 3 of IntFin (n :: Fin 5) -> "good"; _ -> "bad"
-- "good"
--
-- >>> case 3 of IntFin (n :: Fin 3) -> "good"; _ -> "bad"
-- "bad"
pattern IntFin :: KnownNat n => Fin n -> Int
pattern IntFin i <- (toFin -> Just i) where
  IntFin x = fromFin x

data Fin' (n :: Nat) where
  FZ'      :: Fin' (S n)
  FS'      :: Fin n -> Fin' (S n)

upFin :: Fin n -> Fin' n
upFin (UnsafeFin 0) = unsafeCoerce FZ'
upFin (UnsafeFin n) = unsafeCoerce $ FS' $ UnsafeFin (n-1)
{-# inline[0] upFin #-}


{-
knownPred :: forall n r. KnownNat (S n) => (KnownNat n => r) -> r
knownPred r = case someNatVal $ natVal (Proxy :: Proxy (S n)) - 1 of
  SomeNat (Proxy :: Proxy m) -> case unsafeCoerce Refl of
    (Refl :: n :~: m) -> r
-}

-- | A safe pattern for matching 0. A safe, useful basecase.
pattern FZ :: () => forall m. (n ~ S m) => Fin n
pattern FZ <- (upFin -> FZ') where
  FZ = UnsafeFin 0

-- | A safe pattern for matching on the successor. Useful for induction.
pattern FS :: () => forall m. (n ~ S m) => Fin m -> Fin n
pattern FS n <- (upFin -> FS' n) where
  FS n = UnsafeFin (fromFin n + 1)

data KnownFin' (n :: Nat) where
  KnownFZ' :: KnownNat n => KnownFin' (S n)
  KnownFS' :: KnownNat n => Fin n -> KnownFin' (S n)

upKnownFin :: forall n. KnownNat n => Fin n -> KnownFin' n
upKnownFin = case someNatVal $ natVal (Proxy :: Proxy n) - 1 of
  SomeNat (Proxy :: Proxy o) -> case unsafeCoerce Refl of
    (Refl :: n :~: S o) -> \case
      UnsafeFin 0 -> (KnownFZ' :: KnownFin' n)
      UnsafeFin n -> (KnownFS' $ UnsafeFin (n-1) :: KnownFin' n)
{-# inline[0] upKnownFin #-}

-- TODO: could we unify FZ and KnownFZ? e.g. something like
-- @
-- pattern FZ :: forall m. (KnownNat n => KnownNat m, n ~ S m) => Fin n
-- pattern FS :: forall m. (KnownNat n => KnownNat m, n ~ S m) => Fin m -> Fin n
-- @

-- | A safe pattern for matching on the successor. Useful for induction.
--
-- This version calculates KnownNat for the predecessor on a match.
--
-- >>> (case FZ :: Fin 400 of (KnownFZ :: Fin (S k)) -> int @k) :: Int
-- 399
pattern KnownFZ :: KnownNat n => forall m. (KnownNat m, n ~ S m) => Fin n
pattern KnownFZ <- (upKnownFin -> KnownFZ') where
  KnownFZ = UnsafeFin 0

-- | A safe pattern for matching on the successor. Useful for induction.
--
-- This version calculates KnownNat for the predecessor on a match.
--
-- >>> (case FS FZ :: Fin 400 of KnownFS (x :: Fin k) -> int @k) :: Int
-- 399
pattern KnownFS :: KnownNat n => forall m. (KnownNat m, n ~ S m) => Fin m -> Fin n
pattern KnownFS n <- (upKnownFin -> KnownFS' n) where
  KnownFS n = UnsafeFin (fromFin n + 1)

{-# complete FZ, FS :: Fin #-}
{-# complete KnownFZ, KnownFS :: Fin #-}

universe :: forall n. KnownNat n => [Fin n]
universe = UnsafeFin <$> [0 .. int @n - 1]

-- | @'Fin' 0@ is uninhabited
absurdFin :: Fin 0 -> a
absurdFin (Fin _) = error "absurdFin: inhabited Fin 0"
{-# inline absurdFin #-}

cataFin :: forall a n. (a -> a) -> a -> Fin n -> a
cataFin f z = coerce go where
  go :: Int -> a
  go 0 = z
  go k = f $ go $ k-1
{-# inline cataFin #-}

boringFin :: Fin 1
boringFin = FZ
{-# inline boringFin #-}

-- | Return one less.
--
-- >>> isMin (FZ :: Fin 1)
-- Nothing
--
-- >>> map isMin [minBound..maxBound] :: [Maybe (Fin 3)]
-- [Nothing,Just 0,Just 1,Just 2]
--
-- @since 0.1.1
isMin :: Fin (1 + n) -> Maybe (Fin n)
isMin (Fin 0) = Nothing
isMin (Fin n) = Just $ UnsafeFin $ n - 1
{-# inline isMin #-}

-- | >>> map weakenRight1 universe :: [Fin 5]
-- [1,2,3,4]
--
-- @since 0.1.1
weakenRight1 :: Fin n -> Fin (S n)
weakenRight1 = FS
{-# inline weakenRight1 #-}

-- | >>> map weakenLeft1 universe :: [Fin 5]
-- [0,1,2,3]
weakenLeft1 :: Fin n -> Fin (S n)
weakenLeft1 (Fin n) = UnsafeFin n
{-# inline weakenLeft1 #-}

-- | >>> map (weakenRight @2) (universe :: [Fin 3])
-- [2,3,4]
weakenRight :: forall n m. KnownNat n => Fin m -> Fin (n + m)
weakenRight (Fin m) = UnsafeFin $ int @n + m
{-# inline weakenRight #-}

-- | >>> map (weakenLeft @2) (universe :: [Fin 3])
-- [0,1,2]
weakenLeft :: forall m n. Fin n -> Fin (n + m)
weakenLeft (Fin n) = UnsafeFin n
{-# inline weakenLeft #-}

-- | Append two 'Fin's together.
--
-- >>> append (Left (toEnum 2) :: Either (Fin 5) (Fin 4))
-- 2
--
-- >>> append (Right (toEnum 2) :: Either (Fin 5) (Fin 4))
-- 7
append :: forall n m. KnownNat n => Either (Fin n) (Fin m) -> Fin (n + m)
append (Left n)  = weakenLeft @m n
append (Right m) = weakenRight @n m
{-# inline append #-}

-- | Inverse of 'append'.
--
-- >>> split (toEnum 2) :: Either (Fin 2) (Fin 3)
-- Right 0
--
-- >>> split (toEnum 1) :: Either (Fin 2) (Fin 3)
-- Left 1
--
-- >>> map split universe :: [Either (Fin 2) (Fin 3)]
-- [Left 0,Left 1,Right 0,Right 1,Right 2]
--
split :: forall n m. KnownNat n => Fin (n + m) -> Either (Fin n) (Fin m)
split (Fin i)
  | i < n     = Left (UnsafeFin i)
  | otherwise = Right (UnsafeFin $ i - n)
  where n = int @n
{-# inline split #-}

mirrorFin :: forall n. KnownNat n => Fin n -> Fin n
mirrorFin (Fin i) = UnsafeFin (int @n - i - 1)
{-# inline mirrorFin #-}

-- TODO: backport this. if you care. you do it.
#if __GLASGOW_HASKELL__ >= 810

-- |
-- compile time validated numeric literals
--
-- >>> $$(validFin 34) :: Fin 40
-- 34
# if MIN_VERSION_template_haskell(2,17,0)
validFin :: forall n m. (KnownNat n, Quote m, MonadFail m) => Int -> Code m (Fin n)
validFin i
  | i < 0 = Code $ fail "validFin: negative value"
  | i < n = liftTyped (UnsafeFin i)
  | otherwise = Code $ fail $ "validFin: out of bounds: " ++ show i ++ " >= " ++ show n
  where n = int @n
# else
validFin :: forall n. KnownNat n => Int -> Q (TExp (Fin n))
validFin i
  | i < 0 = fail "validFin: negative value"
  | i < n = liftTyped (UnsafeFin i)
  | otherwise = fail $ "validFin: out of bounds: " ++ show i ++ " >= " ++ show n
  where n = int @n
# endif

#endif
