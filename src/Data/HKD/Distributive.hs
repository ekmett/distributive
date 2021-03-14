{-# Language CPP #-}
{-# Language ConstraintKinds #-}
{-# Language DataKinds #-}
{-# Language DefaultSignatures #-}
{-# Language FlexibleContexts #-}
{-# Language StandaloneDeriving #-}
{-# Language DerivingStrategies #-}
{-# Language LiberalTypeSynonyms #-}
{-# Language FlexibleInstances #-}
{-# Language KindSignatures #-}
{-# Language MultiParamTypeClasses #-}
{-# Language PatternSynonyms #-}
{-# Language PolyKinds #-}
{-# Language RankNTypes #-}
{-# Language ScopedTypeVariables #-}
{-# Language Trustworthy #-}
{-# Language TypeFamilies #-}
{-# Language TypeOperators #-}
{-# Language GeneralizedNewtypeDeriving #-}
{-# Language UndecidableInstances #-}
{-# Language UndecidableSuperClasses #-}
{-# Language ViewPatterns #-}

module Data.HKD.Distributive
( type (%)
, FLogarithm(..)
, FTab(..)
, findexLogarithm
, ftabulateLogarithm
, ftabulateRep
, findexRep
, fscatterRep
, fdistrib
, fdistribute
, fcollect
, fcotraverse
, pattern FTabulate

, FDist(..)
, ffmapDist
) where

import Control.Applicative
import Control.Applicative.Backwards
import Data.Distributive
import Data.Distributive.Coerce
import Data.Distributive.Util
import Data.Functor.Compose
import Data.Functor.Identity
import Data.Functor.Product
import Data.Functor.Reverse
import qualified Data.Monoid as Monoid
import Data.Kind
import Data.HKD
import Data.Void
import Data.Proxy
import GHC.Generics
import Data.Coerce

type (%) f g i = f (g i)
infixr 9 %

newtype FLogarithm f a = FLogarithm { runFLogarithm :: forall g. f g -> g a }

newtype FTab g f = FTab { runFTab :: FLogarithm f ~> g }

instance FFunctor (FTab g) where
  ffmap f (FTab k) = FTab (\(FLogarithm j) -> k $ FLogarithm (j . f))
  {-# inline ffmap #-}

class FFunctor f => FDistributive (f :: (k -> Type) -> Type) where
  type FLog f :: k -> Type
  type FLog f = DefaultFLog f

  fscatter :: FFunctor w => (w % Element ~> r) -> (g ~> f) -> w g -> f r
  default fscatter
    :: (Generic1 f, FDistributive (Rep1 f), FFunctor w)
    => (w % Element ~> r) -> (g ~> f) -> w g -> f r
  fscatter = fscatterRep
  {-# inline fscatter #-}

  ftabulate :: (FLog f ~> a) -> f a
  default ftabulate
    :: (Generic1 f, DefaultFTabulate f)
    => (FLog f ~> a) -> f a
  ftabulate = defaultFTabulate (Proxy :: Proxy (ContainsSelfRec1 (Rep1 f) 3))
  {-# inline ftabulate #-}

  findex :: f a -> FLog f ~> a
  default findex
     :: (Generic1 f, DefaultFIndex f)
     => f a -> FLog f ~> a
  findex = defaultFIndex (Proxy :: Proxy (ContainsSelfRec1 (Rep1 f) 3))
  {-# inline findex #-}

fdistrib :: (FFunctor w, FDistributive f) => w f -> (w % Element ~> r) -> f r
fdistrib w k = fscatter k id w
{-# inline fdistrib #-}

ftabulateLogarithm :: FDistributive f => (FLogarithm f ~> a) -> f a
ftabulateLogarithm f = fdistrib (FTab f) $ \(FTab f') -> f' (FLogarithm runElement)
{-# inline ftabulateLogarithm #-}

findexLogarithm :: f a -> FLogarithm f ~> a
findexLogarithm fa (FLogarithm k) = k fa
{-# inline findexLogarithm #-}

ftabulateRep
  :: forall f a.
     (FDistributive (Rep1 f), Generic1 f, Coercible (FLog f) (FLog (Rep1 f)))
  => (FLog f ~> a) -> f a
ftabulateRep f = to1 $ ftabulate (\x -> f (coerce x))
{-# inline ftabulateRep #-}

findexRep
  :: forall f a.
     (FDistributive (Rep1 f), Generic1 f, Coercible (FLog f) (FLog (Rep1 f)))
  => f a -> FLog f ~> a
findexRep fa flog = findex (from1 fa) (coerce flog)
{-# inline findexRep #-}

fscatterRep
  :: (FDistributive (Rep1 f), Generic1 f, FFunctor w)
  => (w % Element ~> r) -> (g ~> f) -> w g -> f r
fscatterRep k phi = to1 . fscatter k (from1 . phi)
{-# inline fscatterRep #-}

pattern FTabulate :: FDistributive f => (FLog f ~> a) -> f a
pattern FTabulate i <- (findex -> i) where
  FTabulate i = ftabulate i

type family DefaultFLog' (containsRec1 :: Bool) (f :: (i -> Type) -> Type) :: i -> Type where
  DefaultFLog' 'True  f = FLogarithm f
  DefaultFLog' 'False f = FLog (Rep1 f)

type family DefaultFImplC (containsRec1 :: Bool) f :: Constraint where
  DefaultFImplC 'True  f = (FDistributive f, FLog f ~ FLogarithm f)
  DefaultFImplC 'False f = (Generic1 f, FDistributive (Rep1 f), Coercible (FLog f) (FLog (Rep1 f)))

-- individual type classes, so there is GHC needs to less work
class DefaultFImplC containsRec1 f => DefaultFTabulate' (containsRec1 :: Bool) f where
  defaultFTabulate :: Proxy containsRec1 -> (FLog f ~> a) -> f a

instance DefaultFImplC 'True f => DefaultFTabulate' 'True f where
  defaultFTabulate _ = ftabulateLogarithm
  {-# inline defaultFTabulate #-}

instance DefaultFImplC 'False f => DefaultFTabulate' 'False f where
  defaultFTabulate _ = ftabulateRep
  {-# inline defaultFTabulate #-}

class DefaultFImplC containsRec1 f => DefaultFIndex' (containsRec1 :: Bool) f where
  defaultFIndex :: Proxy containsRec1 -> f a -> FLog f ~> a

instance DefaultFImplC 'True f => DefaultFIndex' 'True f where
  defaultFIndex _ = findexLogarithm
  {-# inline defaultFIndex #-}

instance DefaultFImplC 'False f => DefaultFIndex' 'False f where
  defaultFIndex _ = findexRep
  {-# inline defaultFIndex #-}

type DefaultFLog f = DefaultFLog' (ContainsSelfRec1 (Rep1 f) 3) f
type DefaultFTabulate f = DefaultFTabulate' (ContainsSelfRec1 (Rep1 f) 3) f
type DefaultFIndex f = DefaultFIndex' (ContainsSelfRec1 (Rep1 f) 3) f

-- | 
--
-- @
-- 'fdistribute' = 'fcollect' 'id'
-- @
fdistribute
  :: (Functor f, FDistributive g)
  => f (g a) -> g (Compose f a)
fdistribute f = fdistrib (DCompose f) $ \(DCompose f') -> Compose $ fmap coerce f'
{-# inline fdistribute #-}

-- |
-- @
-- 'fcollect' f = 'fdistribute' . 'fmap' f
-- @
fcollect
  :: (Functor f, FDistributive g)
  => (a -> g b)
  -> f a -> g (Compose f b)
fcollect f fa = fdistrib (DCompose f) $ \(DCompose f') -> Compose $ fmap (coerce f') fa
{-# inline fcollect #-}

-- |
-- @
-- 'fcotraverse' f = 'fmap' f . 'fdistribute'
-- @
fcotraverse
  :: (Functor f, FDistributive g)
  => (f % a ~> b)
  -> f (g a) -> g b
fcotraverse fab fga = fdistrib (DCompose fga) $ \(DCompose f') -> fab (fmap coerce f')
{-# inline fcotraverse #-}

instance (FDistributive f, FDistributive g) => FDistributive (f :*: g) where
  type FLog (f :*: g) = FLog f :+: FLog g
  fscatter k f (ffmap f -> w)
      = fscatter k (\(l :*: _) -> l) w
    :*: fscatter k (\(_ :*: r) -> r) w
  ftabulate f = ftabulate (f . L1) :*: ftabulate (f . R1)
  findex (f :*: _) (L1 x) = findex f x
  findex (_ :*: g) (R1 y) = findex g y
  {-# inline fscatter #-}
  {-# inline ftabulate #-}
  {-# inline findex #-}

instance FDistributive f => FDistributive (M1 i c f) where
  type FLog (M1 i c f) = FLog f
  fscatter k f = M1 #. fscatter k (unM1 #. f)
  findex (M1 f) = findex f
  ftabulate f = M1 $ ftabulate f
  {-# inline fscatter #-}
  {-# inline ftabulate #-}
  {-# inline findex #-}

instance FDistributive U1 where
  type FLog U1 = Const Void
  fscatter _ _ _ = U1
  ftabulate _ = U1
  findex _ = absurd .# getConst
  {-# inline fscatter #-}
  {-# inline ftabulate #-}
  {-# inline findex #-}

instance FDistributive f => FDistributive (Rec1 f) where
  type FLog (Rec1 f) = FLog f
  fscatter k f = Rec1 #. fscatter k (unRec1 #. f)
  findex (Rec1 f) = findex f
  ftabulate f = Rec1 $ ftabulate f
  {-# inline fscatter #-}
  {-# inline ftabulate #-}
  {-# inline findex #-}

instance (Distributive f, FDistributive g) => FDistributive (f :.: g) where
  type FLog (f :.: g) = Const (Log f) :*: FLog g
  fscatter k phi wg = Comp1 $ scatter (fscatter k coerce .# runAppCompose) id (AppCompose (ffmap phi wg))
  findex (Comp1 f) (Const x :*: y) = findex (index f x) y
  ftabulate f = Comp1 $ tabulate $ \i -> ftabulate $ \j -> f (Const i :*: j)
  {-# inline fscatter #-}
  {-# inline ftabulate #-}
  {-# inline findex #-}

instance (Distributive f, FDistributive g) => FDistributive (Compose f g) where
  type FLog (Compose f g) = FLog (Rep1 (Compose f g))
  findex = findexRep
  ftabulate = ftabulateRep
  {-# inline ftabulate #-}
  {-# inline findex #-}

instance (FDistributive f, FDistributive g) => FDistributive (Product f g) where
  type FLog (Product f g) = FLog (Rep1 (Product f g))
  findex = findexRep
  {-# inline findex #-}
  ftabulate = ftabulateRep
  {-# inline ftabulate #-}

instance FDistributive Proxy

deriving newtype instance FDistributive f => FDistributive (Backwards f)
deriving newtype instance FDistributive f => FDistributive (Reverse f)
deriving newtype instance FDistributive f => FDistributive (Monoid.Alt f)

#if MIN_VERSION_base(4,12,0)
-- Ap was only added in base 4.12 ghc 8.6
deriving newtype instance FDistributive f => FDistributive (Monoid.Ap f)
#endif

newtype FDist f a = FDist { runFDist :: f a }
  deriving newtype (FFoldable)

instance (FDistributive f, FTraversable f) => FTraversable (FDist f) where
  ftraverse f = fmap FDist . ftraverse f .# runFDist
  {-# inline ftraverse #-}

deriving newtype instance FDistributive f => FDistributive (FDist f)

-- | A default definition for 'ffmap' from 'FFunctor' in terms of 'FDistributive'
ffmapDist :: FDistributive f => (a ~> b) -> f a -> f b
ffmapDist f = fscatter (f .# (runElement . runElement)) id .# Element
{-# inline ffmapDist #-}

instance FDistributive f => FFunctor (FDist f) where
  ffmap = ffmapDist
  {-# inline ffmap #-}

instance FDistributive f => FZip (FDist f) where
  fzipWith = fzipWithDist
  {-# inline fzipWith #-}

fzipWithDist :: FDistributive f => (forall x. a x -> b x -> c x) -> f a -> f b -> f c
fzipWithDist f m n = fdistrib (D2 m n) $ \(D2 (Element m') (Element n')) -> f m' n'
{-# inline fzipWithDist #-}

instance FDistributive f => FRepeat (FDist f) where
  frepeat = frepeatDist
  {-# inline frepeat #-}

frepeatDist :: FDistributive f => (forall x. a x) -> f a
frepeatDist ax = fscatter (\x -> runLimit (getConst x)) id (Const (Limit ax))
-- frepeatDist a = fdistrib Proxy $ \_ -> a
{-# inline frepeatDist #-}
