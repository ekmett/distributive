{-# Language Unsafe #-}
{-# Language BangPatterns #-}
{-# Language KindSignatures #-}
{-# Language ScopedTypeVariables #-}
{-# Language TypeApplications #-}
{-# Language GADTs #-}
{-# Language RankNTypes #-}
{-# Language FlexibleContexts #-}
{-# Language FlexibleInstances #-}
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
{-# options_haddock hide #-}
module Data.HKD.Distributive.Internal.Record where

import Control.Applicative
import Data.Distributive.Internal.Coerce
import Data.Distributive.Util
import Data.Functor.Classes
import Data.HKD
import Data.HKD.Distributive
import Data.HKD.Distributive.Internal.Index
import Data.HKD.WithIndex
import Data.Kind
import qualified Data.Monoid as Monoid
import Data.Proxy
import Data.Traversable.WithIndex
import Data.Type.Equality
import Data.Vector as V
import GHC.Exts
import GHC.TypeNats
import Unsafe.Coerce

type role Record nominal representational
newtype Record (as :: [i]) (f :: i -> Type) = UnsafeRecord
  { safeRecord :: Vector Any
  }

instance FFunctor (Record as) where
  ffmap f = UnsafeRecord #. V.map (unsafeCoerce f) .# safeRecord
  {-# inline ffmap #-}

instance FFunctorWithIndex (Index as) (Record as) where
  ifmap f = UnsafeRecord #. V.imap (unsafeCoerce f) .# safeRecord
  {-# inline ifmap #-}

instance FFoldable (Record as) where
  ffoldMap f = V.foldMap (unsafeCoerce f) .# safeRecord
  {-# inline ffoldMap #-}

instance FFoldableWithIndex (Index as) (Record as) where
  iffoldMap f = V.ifoldr (\i a r -> f (UnsafeIndex i) (unsafeCoerce a) <> r) mempty .# safeRecord
  {-# inline iffoldMap #-}

instance FTraversable (Record as) where
  ftraverse = \(f :: forall x. f x -> m (g x)) ->
    fmap UnsafeRecord .
    traverse (\a -> Any <$> f (unsafeCoerce a)) .# safeRecord
  {-# inline ftraverse #-}

instance FTraversableWithIndex (Index as) (Record as) where
  iftraverse = \f (UnsafeRecord xs) ->
    let !n = V.length xs
    in (UnsafeRecord #. V.fromListN n) <$>
    itraverse (\i a -> Any <$> f (UnsafeIndex i) (unsafeCoerce a)) (V.toList xs)
  {-# inline iftraverse #-}

instance KnownLength as => FDistributive (Record as) where
  type FLog (Record as) = Index as
  fscatter k f (ffmap f -> w) =
    UnsafeRecord $
      generate (len @as) $ \i ->
        Any $ k $ ffmap (\r -> Element $ findex r (UnsafeIndex i)) w
  {-# inline fscatter #-}
  findex (UnsafeRecord as) (UnsafeIndex i) = unsafeCoerce (as ! i)
  {-# inline findex #-}
  ftabulate f = UnsafeRecord $ generate (len @as) $ \i -> Any $ f (UnsafeIndex i)
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

instance (p a, All p as) => All (p :: i -> Constraint) (a ': as) where
  para nil kons = kons (proxy# @a) (para @i @p nil kons)

withLen :: forall as f r. Record as f -> (KnownLength as => r) -> r
withLen v r = case someNatVal (fromIntegral $ V.length (safeRecord v)) of
  SomeNat (Proxy :: Proxy n') -> case unsafeCoerce Refl of
    (Refl :: Length as :~: n') -> r

data IRec (f :: i -> Type) (as :: [i]) = IRec {-# unpack #-} !Int [Any]

cfdistrib
  :: forall i (p :: i -> Constraint) (as :: [i]) (r :: i -> Type) w.
     (All p as, KnownLength as, FFunctor w)
  => w (Record as)
  -> (forall x. p x => w (Element x) -> r x)
  -> Record as r
cfdistrib w k = case len @as of
  n -> case para @i @p @as (IRec n [])
          $ \ (_ :: Proxy# b) (IRec (subtract 1 -> i) t) ->
              IRec i $
                (Any $ k $ ffmap (\(r :: Record as a) ->
                Element $ findex r (UnsafeIndex i) :: Element b a) w) : t
         of
    IRec 0 r -> UnsafeRecord $ V.fromListN n r
    _ -> error "cfdistrib: the impossible happened"
{-# inline cfdistrib #-}

instance (Eq1 f, All Eq as) => Eq (Record as f) where
  xs == ys =
    Monoid.getAll $
    ffoldMap getConst $
    withLen xs $
    cfdistrib @Type @Eq (D2 xs ys) $
    \(D2 (Element x) (Element y)) ->
    Const $ Monoid.All $ liftEq (==) x y

instance (Ord1 f, All Ord as, All Eq as) => Ord (Record as f) where
  compare xs ys =
    ffoldMap getConst $
    withLen xs $
    cfdistrib @Type @Ord (D2 xs ys) $
    \(D2 (Element x) (Element y)) ->
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

