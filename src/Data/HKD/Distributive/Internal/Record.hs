{-# Language CPP #-}
{-# Language Unsafe #-}
{-# Language BangPatterns #-}
{-# Language KindSignatures #-}
{-# Language ScopedTypeVariables #-}
{-# Language TypeApplications #-}
{-# Language GADTs #-}
{-# Language RankNTypes #-}
{-# Language FlexibleContexts #-}
{-# Language FlexibleInstances #-}
{-# Language DefaultSignatures #-}
{-# Language UndecidableInstances #-}
{-# Language MagicHash #-}
{-# Language RoleAnnotations #-}
{-# Language UndecidableSuperClasses #-}
{-# Language MultiParamTypeClasses #-}
{-# Language PartialTypeSignatures #-}
{-# Language TypeFamilies #-}
{-# Language DataKinds #-}
{-# Language PolyKinds #-}
{-# Language StandaloneDeriving #-}
{-# Language PatternSynonyms #-}
{-# Language ViewPatterns #-}
{-# Language ConstraintKinds #-}
{-# Language DerivingVia #-}
{-# Language TypeOperators #-}
{-# Language GeneralizedNewtypeDeriving #-}
#if __GLASGOW_HASKELL__ >= 806
{-# Language QuantifiedConstraints #-}
#endif
{-# options_haddock hide #-}
module Data.HKD.Distributive.Internal.Record where

import Control.Applicative
import Data.Distributive
import Data.Distributive.Internal.Coerce
import Data.Functor.Classes
import Data.Functor.Compose
import Data.Functor.Product
import Data.HKD
import Data.HKD.Distributive
import Data.HKD.Distributive.Internal.Index
import Data.HKD.WithIndex
import Data.Kind
import qualified Data.Monoid as Monoid
import Data.Proxy
import Data.Some
import Data.Traversable.WithIndex
import Data.Type.Equality
import Data.Vector as V
import GHC.Exts
import GHC.Generics
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

instance KnownLength as => FDistributive (Record as) where
  type FLog (Record as) = Index as
  fscatter k f (ffmap f -> w) =
    UnsafeRecord $
    generate (len @as) $ \i ->
    Any $ k $ ffmap (\r -> F1 $ findex r (UnsafeIndex i)) w
  {-# inline fscatter #-}
  findex (UnsafeRecord as) (UnsafeIndex i) = unsafeCoerce (as ! i)
  {-# inline findex #-}
  ftabulate f =
    UnsafeRecord $
    generate (len @as) $ \i ->
    Any $ f (UnsafeIndex i)
  {-# inline ftabulate #-}

instance FZip (Record as) where
  fzipWith f as =
    UnsafeRecord #.
    V.zipWith (unsafeCoerce f) (safeRecord as) .#
    safeRecord
  {-# inline fzipWith #-}

deriving via FDist (Record as) instance KnownLength as => FRepeat (Record as)

type family AllF (p :: i -> Constraint) (as :: [i]) :: Constraint where
  AllF _ '[] = ()
  AllF p (a ': as) = (p a, AllF p as)

class AllF p as => All (p :: i -> Constraint) (as :: [i]) where
  para :: r '[] -> (forall b bs. (p b, All p bs) => Proxy# b -> r bs -> r (b ': bs)) -> r as

instance All p '[] where
  para nil _ = nil
  {-# inline para #-}

instance (p a, All p as) => All (p :: i -> Constraint) (a ': as) where
  para nil kons = kons (proxy# @a) (para @i @p nil kons)
  {-# inline para #-}

withLen :: forall as f r. Record as f -> (KnownLength as => r) -> r
withLen v r = case someNatVal (fromIntegral $ V.length (safeRecord v)) of
  SomeNat (Proxy :: Proxy n') -> case unsafeCoerce Refl of
    (Refl :: Length as :~: n') -> r
{-# inline withLen #-}


class GAll (p :: i -> Constraint) (f :: (i -> Type) -> Type) where
  gall :: f (Dict1 p)
  default gall :: (Generic1 f, GAll p (Rep1 f)) => f (Dict1 p)
  gall = to1 gall

instance (GAll p f, GAll p g) => GAll p (f :*: g) where
  gall = gall :*: gall

instance (Distributive f, GAll p g) => GAll p (f :.: g) where
  gall = Comp1 $ pureDist gall

deriving newtype instance GAll p f => GAll p (M1 i c f)
deriving newtype instance GAll p f => GAll p (Rec1 f)

instance GAll p U1 where gall = U1

instance GAll p Proxy

instance a ~ Dict1 p => GAll p ((:~:) a) where
  gall = Refl
instance p a => GAll p (F1 a) where
  gall = F1 Dict1
instance (p a, p b) => GAll p (F2 a b) where
  gall = F2 Dict1 Dict1
instance (p a, p b, p c) => GAll p (F3 a b c) where
  gall = F3 Dict1 Dict1 Dict1
instance (p a, p b, p c, p d) => GAll p (F4 a b c d) where
  gall = F4 Dict1 Dict1 Dict1 Dict1
instance (p a, p b, p c, p d, p e) => GAll p (F5 a b c d e) where
  gall = F5 Dict1 Dict1 Dict1 Dict1 Dict1
instance q (Dict1 p) => GAll p (Dict1 q) where
  gall = Dict1

instance (Distributive f, GAll p g) => GAll p (Compose f g)

instance (GAll p f, GAll p g) => GAll p (Product f g)

#if __GLASGOW_HASKELL__ >= 806
-- this is arguably any existential constraint
instance (forall a. p a) => GAll p Some where gall = Some Dict1
instance (forall a. p a) => GAll p Limit where gall = Limit Dict1
instance (forall a. q a => p a) => GAll p (FConstrained q) where
  gall = FConstrained Dict1
#else
instance p ~ q => GAll p (FConstrained q) where
  gall = FConstrained Dict1
#endif

data IRec (f :: i -> Type) (as :: [i]) = IRec {-# unpack #-} !Int [Any]

gcfdistrib
  :: forall i (p :: i -> Constraint) (f :: (i -> Type) -> Type) (r :: i -> Type) w.
     (GAll p f, FFunctor w)
  => w f
  -> (forall x. p x => w (F1 x) -> r x)
  -> f r
gcfdistrib _ _ = undefined


cfdistrib
  :: forall i (p :: i -> Constraint) (as :: [i]) (r :: i -> Type) w.
     (All p as, KnownLength as, FFunctor w)
  => w (Record as)
  -> (forall x. p x => w (F1 x) -> r x)
  -> Record as r
cfdistrib w k = case len @as of
  n ->
    case
      para @i @p @as (IRec n []) $
      \ (_ :: Proxy# b) (IRec (subtract 1 -> i) t) ->
        IRec i $
          (Any $ k $
            ffmap
              (\(r :: Record as a) -> F1 $ findex r (UnsafeIndex i) :: F1 b a)
              w
          ) : t
    of
    IRec 0 r -> UnsafeRecord $ V.fromListN n r
    _ -> error "cfdistrib: the impossible happened"
{-# inline cfdistrib #-}

instance (Eq1 f, All Eq as) => Eq (Record as f) where
  xs == ys =
    Monoid.getAll $
    ffoldMap getConst $
    withLen xs $
    cfdistrib @Type @Eq (F2 xs ys) $
    \(F2 (F1 x) (F1 y)) ->
    Const $ Monoid.All $ liftEq (==) x y

instance (Ord1 f, All Ord as, All Eq as) => Ord (Record as f) where
  compare xs ys =
    ffoldMap getConst $
    withLen xs $
    cfdistrib @Type @Ord (F2 xs ys) $
    \(F2 (F1 x) (F1 y)) ->
    Const $ liftCompare compare x y

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

