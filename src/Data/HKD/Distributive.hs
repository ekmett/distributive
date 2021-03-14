{-# Language CPP #-}
{-# Language ConstraintKinds #-}
{-# Language DataKinds #-}
{-# Language DefaultSignatures #-}
{-# Language FlexibleContexts #-}
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
{-# Language UndecidableInstances #-}
{-# Language UndecidableSuperClasses #-}
{-# Language ViewPatterns #-}

module Data.HKD.Distributive where

import Data.Distributive.Util
import Data.Functor.Compose
import Data.Kind
import Data.HKD hiding (type (~>))
import Data.Proxy
import GHC.Generics
import Data.Coerce

type (.) f g i = f (g i)
infixr 9 .

type f ~> g = forall i. f i -> g i
infixr 0 ~>

newtype FLogarithm f a = FLogarithm { runFLogarithm :: forall g. f g -> g a }

newtype FTab g f = FTab { runFTab :: FLogarithm f ~> g }

instance FFunctor (FTab g) where
  ffmap f (FTab k) = FTab (\(FLogarithm j) -> k $ FLogarithm (j . f))

class FFunctor f => FDistributive (f :: (k -> Type) -> Type) where
  type FLog f :: k -> Type
  type FLog f = DefaultFLog f

  fscatter :: FFunctor w => (w . Element ~> r) -> (g ~> f) -> w g -> f r
  default fscatter
    :: (Generic1 f, FDistributive (Rep1 f), FFunctor w)
    => (w . Element ~> r) -> (g ~> f) -> w g -> f r
  fscatter = fscatterRep

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

fdistrib :: (FFunctor w, FDistributive f) => w f -> (w . Element ~> r) -> f r
fdistrib w k = fscatter k id w

ftabulateLogarithm :: FDistributive f => (FLogarithm f ~> a) -> f a
ftabulateLogarithm f = fdistrib (FTab f) $ \(FTab f') -> f' (FLogarithm runElement)

findexLogarithm :: f a -> FLogarithm f ~> a
findexLogarithm fa (FLogarithm k) = k fa

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
  => (w . Element ~> r) -> (g ~> f) -> w g -> f r
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

-- | The dual of 'Data.Traversable.sequenceA'
--
-- >>> distribute [(+1),(+2)] 1
-- [2,3]
--
-- @
-- 'distribute' = 'collect' 'id'
-- 'distribute' . 'distribute' = 'id'
-- @
fdistribute
  :: (Functor f, FDistributive g)
  => f (g a) -> g (Compose f a)
fdistribute f = fdistrib (DCompose f) $ \(DCompose f') -> Compose $ fmap coerce f'
{-# inline fdistribute #-}

-- |
-- @
-- 'collect' f = 'distribute' . 'fmap' f
-- 'fmap' f = 'runIdentity' . 'collect' ('Identity' . f)
-- 'fmap' 'distribute' . 'collect' f = 'getCompose' . 'collect' ('Compose' . f)
-- @
fcollect
  :: (Functor f, FDistributive g)
  => (a -> g b)
  -> f a -> g (Compose f b)
fcollect f fa = fdistrib (DCompose f) $ \(DCompose f') -> Compose $ fmap (coerce f') fa
{-# inline fcollect #-}

-- | The dual of 'Data.Traversable.traverse'
--
-- @
-- 'cotraverse' f = 'fmap' f . 'distribute'
-- @
fcotraverse
  :: (Functor f, FDistributive g)
  => (f . a ~> b)
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

{-
instance FDistributive f => FDistributive (M1 i c f) where
  type FLog (M1 i c f) = FLog f
  fscatter k f = M1 #. fscatter k (unM1 #. f)
  findex = findex .# unM1
  ftabulate = M1 #. ftabulate
  {-# inline fscatter #-}
  {-# inline ftabulate #-}
  {-# inline findex #-}
-}


newtype FDist f a = FDist { runFDist :: f a }
