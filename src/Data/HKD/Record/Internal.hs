{-# Language DerivingVia #-}
{-# Language Unsafe #-}
{-# options_haddock not-home #-}

-- |
-- Copyright   : (C) 2021 Edward Kmett,
-- License     : BSD-2-Style OR Apache-2.0
-- Maintainer  : Edward Kmett <ekmett@gmail.com>
-- Stability   : provisional
-- Portability : non-portable

module Data.HKD.Record.Internal where

import Control.Applicative
import Data.Function.Coerce
import Data.HKD
import Data.HKD.Index.Internal
import Data.HKD.Rep
import Data.Kind
import Data.Proxy
import Data.Traversable.WithIndex
import Data.Type.Equality
import Data.Vec.Internal
import Data.Vector as V
import GHC.Exts
import GHC.TypeNats
import Unsafe.Coerce

type role Record nominal representational
newtype Record (as :: [i]) (f :: i -> Type) = UnsafeRecord
  { safeRecord :: Vector Any
  }

instance FFunctor (Record as) where
  ffmap f =
    UnsafeRecord #.
    V.map (unsafeCoerce f) .#
    safeRecord
  {-# inline ffmap #-}

instance FFunctorWithIndex (Index as) (Record as) where
  ifmap f =
    UnsafeRecord #.
    V.imap (unsafeCoerce f) .#
    safeRecord
  {-# inline ifmap #-}

instance FFoldable (Record as) where
  ffoldMap f =
    V.foldMap (unsafeCoerce f) .#
    safeRecord
  {-# inline ffoldMap #-}

instance FFoldableWithIndex (Index as) (Record as) where
  iffoldMap f =
    V.ifoldr (\i a r -> f (UnsafeIndex i) (unsafeCoerce a) <> r) mempty .#
    safeRecord
  {-# inline iffoldMap #-}

instance FTraversable (Record as) where
  ftraverse = \(f :: forall x. f x -> m (g x)) ->
    fmap UnsafeRecord .
    traverse(\a -> Any <$> f (unsafeCoerce a)) .#
    safeRecord
  {-# inline ftraverse #-}

instance FTraversableWithIndex (Index as) (Record as) where
  iftraverse = \f (UnsafeRecord xs) ->
    let !n = V.length xs
    in (UnsafeRecord #. V.fromListN n) <$>
    itraverse
      (\i a -> Any <$> f (UnsafeIndex i) (unsafeCoerce a))
      (V.toList xs)
  {-# inline iftraverse #-}

instance FIndexable (Record as) where
  type FLog (Record as) = Index as
  findex (UnsafeRecord as) (UnsafeIndex i) = unsafeCoerce (as ! i)
  {-# inline findex #-}

instance KnownLength as => FRepresentable (Record as) where
  fscatter k f (ffmap f -> w) =
    UnsafeRecord $
    generate (len @as) \i ->
    Any $ k $ ffmap (\r -> F1 $ findex r (UnsafeIndex i)) w
  {-# inline fscatter #-}
  ftabulate f =
    UnsafeRecord $
    generate (len @as) (Any . f .# UnsafeIndex)
  {-# inline ftabulate #-}

instance FApply (Record as) where
  fliftA2 f as =
    UnsafeRecord #.
    V.zipWith (unsafeCoerce f) (safeRecord as) .#
    safeRecord
  {-# inline fliftA2 #-}

deriving via FDist (Record as) instance KnownLength as => FApplicative (Record as)

type family AllF (p :: i -> Constraint) (as :: [i]) :: Constraint where
  AllF _ '[] = ()
  AllF p (a ': as) = (p a, AllF p as)

class AllF p as => All (p :: i -> Constraint) (as :: [i]) where
  para :: r '[] -> (forall b bs. (p b, All p bs) => Proxy# b -> r bs -> r (b ': bs)) -> r as

instance All p '[] where
  para nil _ = nil
  {-# inline para #-}

instance (p a, All p as) => All (p :: i -> Constraint) (a ': as) where
  para nil kons = kons (proxy# :: Proxy# a) (para @i @p nil kons)
  {-# inline para #-}

withLen :: forall as f r. Record as f -> (KnownLength as => r) -> r
withLen v r = case someNatVal (fromIntegral $ V.length (safeRecord v)) of
  SomeNat (Proxy :: Proxy n') -> case unsafeCoerce Refl of
    (Refl :: Length as :~: n') -> r
{-# inline withLen #-}

data IRec (f :: i -> Type) (as :: [i]) = IRec {-# unpack #-} !Int [Any]

instance (KnownLength as, All p as) => FAll (p :: i -> Constraint) (Record as) where
  fall = case len @as of
    n ->
      case para @i @p @as (IRec n []) $
      \ (_ :: Proxy# b) (IRec (subtract 1 -> i) t) ->
        IRec i $ Any (Dict1 :: Dict1 p b) : t
      of
      IRec 0 r -> UnsafeRecord $ V.fromListN n r
      _ -> error "Data.HKD.Internal.Record.fall: the impossible happened"
  {-# inline[0] fall #-}

{-
instance (EqC f, All EqC as) => Eq (Record (as :: [Type]) f) where
  xs == ys =
    withLen xs $
    Monoid.getAll $
    ffoldMap getConst $
    fliftD3
      (\Dict1 x y -> Const $ Monoid.All $ x == y)
      (fall @_ @Eq) xs ys

instance (EqC f, All EqC as) => Eq (Record (as :: [Type]) f) where
  xs == ys =
    withLen xs $
    Monoid.getAll $
    ffoldMap getConst $
    fliftD3
      (\Dict1 x y -> Const $ Monoid.All $ x == y)
      (fall @_ @Eq) xs ys
-}

{-
instance (Eq1 f, All Eq as) => Eq (Record (as :: [Type]) f) where
  xs == ys = Monoid.getAll $
  {-# inline (==) #-}

instance (Ord1 f, All Ord as, All Eq as) => Ord (Record (as :: [Type]) f) where
  compare xs ys =
    ffoldMap getConst $
    withLen xs $
    fliftD3
      (\Dict1 x y -> Const $ liftCompare compare x y)
      (fall @Type @Ord) xs ys
  {-# inline compare #-}
-}

data Record' :: [i] -> (i -> Type) -> Type where
  Nil' :: Record' '[] f
  Cons' :: f a -> Record as f -> Record' (a ': as) f

upRecord :: Record as f -> Record' as f
upRecord (UnsafeRecord xs)
  | V.length xs == 0 = unsafeCoerce Nil'
  | otherwise = unsafeCoerce Cons' (xs V.! 0) (UnsafeRecord (V.tail xs))

pattern Nil :: () => as ~ '[] => Record as f
pattern Nil <- (upRecord -> Nil') where
  Nil = UnsafeRecord V.empty

-- TODO: construction
pattern Cons :: () => (as ~ (b ': bs)) => f b -> Record bs f -> Record as f
pattern Cons b bs <- (upRecord -> Cons' b bs) -- where
--  Cons b bs = undefined

pattern Any :: a -> Any
pattern Any a <- (unsafeCoerce -> a) where
  Any a = unsafeCoerce a

liftVec :: Vec (Length as) a -> Record as (Const a)
liftVec (Vec as) = UnsafeRecord (unsafeCoerce as)
{-# inline liftVec #-}

lowerVec :: Record as (Const a) -> Vec (Length as) a
lowerVec (UnsafeRecord as) = UnsafeVec (unsafeCoerce as)
{-# inline lowerVec #-}
