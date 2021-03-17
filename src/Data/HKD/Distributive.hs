{-# Language CPP #-}
{-# Language AllowAmbiguousTypes #-}
{-# Language ConstraintKinds #-}
{-# Language DataKinds #-}
{-# Language DefaultSignatures #-}
{-# Language DeriveDataTypeable #-}
{-# Language DeriveGeneric #-}
{-# Language DerivingStrategies #-}
{-# Language EmptyCase #-}
{-# Language ExistentialQuantification #-}
{-# Language FlexibleContexts #-}
{-# Language FlexibleInstances #-}
{-# Language GADTs #-}
{-# Language GeneralizedNewtypeDeriving #-}
{-# Language KindSignatures #-}
{-# Language LambdaCase #-}
{-# Language LiberalTypeSynonyms #-}
{-# Language MultiParamTypeClasses #-}
{-# Language PatternSynonyms #-}
{-# Language PolyKinds #-}
{-# Language RankNTypes #-}
{-# Language RoleAnnotations #-}
{-# Language ScopedTypeVariables #-}
{-# Language StandaloneDeriving #-}
{-# Language Trustworthy #-}
{-# Language TypeApplications #-}
{-# Language TypeFamilies #-}
{-# Language TypeInType #-}
{-# Language TypeOperators #-}
{-# Language UndecidableInstances #-}
{-# Language UndecidableSuperClasses #-}
{-# Language ViewPatterns #-}

#ifndef MIN_VERSION_base
#define MIN_VERSION_Base(_x,_y,_z) 1
#endif

module Data.HKD.Distributive
( type (%)
, FDistributive(..)
, fdistribute
, fcotrav
, fdistrib
, fcollect
, fcotraverse
, pattern FTabulate
-- * DerivingVia
, FDist(..)
-- * FFunctor
, ffmapFDist
-- * FRepeat
, frepeatFDist
-- * FZip
, fzipWithFDist
-- * Others
, faskFDist
, ftraceFDist
, ifmapFDist
, iffoldMapFDist
, iftraverseFDist
-- * Default logarithms
, FLogarithm(..)
, FTab(..)
, findexFLogarithm
, ftabulateFLogarithm
, ftabulateRep
, findexRep
, fscatterRep
, fscatterDefault

-- * Uniqueness of logarithms
, flogToFLogarithm
, flogFromFLogarithm
, geqFLog
, gcompareFLog

-- * Logarithm lens
, _flogarithm
, _flog
, _flogGEq

-- * LKD
, LKD(..)
, lowerLogarithm
, liftLogarithm

-- * HKD
, HKD(..)
, Atkey(..)
) where

import Control.Applicative
import Control.Applicative.Backwards
import Data.Data
import Data.Distributive
import Data.Distributive.Internal.Coerce
import Data.Distributive.Util
import Data.Foldable.WithIndex
import Data.Functor.Compose
import Data.Functor.Identity
import Data.Functor.Product
import Data.Functor.Reverse
import Data.Functor.Contravariant
import Data.Functor.Contravariant.Divisible
import Data.Functor.WithIndex
import Data.GADT.Compare
import qualified Data.Monoid as Monoid
import Data.Kind
import Data.HKD
import Data.HKD.Divisible
import Data.HKD.WithIndex
import Data.Some
import Data.Traversable.WithIndex
import Data.Type.Coercion
import Data.Type.Equality
import Data.Void
import GHC.Generics
import GHC.Types
import Data.Coerce
import Data.Function
import Unsafe.Coerce

type (%) f g i = f (g i)
infixr 9 %

-- | A higher-kinded 'Logarithm'
--
type role FLogarithm representational nominal
newtype FLogarithm f a = FLogarithm { runFLogarithm :: forall g. f g -> g a }

-- | A higher-kinded 'Tab'
type role FTab representational representational
newtype FTab g f = FTab { runFTab :: FLogarithm f ~> g }

instance FFunctor (FTab g) where
  ffmap f (FTab k) = FTab (\(FLogarithm j) -> k $ FLogarithm (j . f))
  {-# inline ffmap #-}

class FFunctor f => FDistributive (f :: (k -> Type) -> Type) where
  -- | A higher-kinded 'Log'
  type FLog f :: k -> Type
  type FLog f = DefaultFLog f

  -- | A higher-kinded 'scatter'
  fscatter :: FFunctor w => (w % F1 ~> r) -> (g ~> f) -> w g -> f r
  default fscatter
    :: (Generic1 f, FDistributive (Rep1 f), FFunctor w)
    => (w % F1 ~> r) -> (g ~> f) -> w g -> f r
  fscatter = fscatterRep
  {-# inline fscatter #-}

  -- | A higher-kinded 'tabulate'
  ftabulate :: (FLog f ~> a) -> f a
  default ftabulate
    :: (Generic1 f, DefaultFTabulate f)
    => (FLog f ~> a) -> f a
  ftabulate = defaultFTabulate @(ContainsSelfRec1 (Rep1 f) 3)
  {-# inline ftabulate #-}

  -- | A higher-kinded 'index'
  findex :: f a -> FLog f ~> a
  default findex
     :: (Generic1 f, DefaultFIndex f)
     => f a -> FLog f ~> a
  findex = defaultFIndex @(ContainsSelfRec1 (Rep1 f) 3)
  {-# inline findex #-}

-- | A higher-kinded 'cotrav'
fcotrav
  :: (FFunctor w, FDistributive f)
  => (w % F1 ~> r) -> w f -> f r
fcotrav = \k -> fscatter k id
{-# inline fcotrav #-}

-- | A higher-kinded 'distrib'
fdistrib
  :: (FFunctor w, FDistributive f)
  => w f -> (w % F1 ~> r) -> f r
fdistrib = \ w k -> fscatter k id w
{-# inline fdistrib #-}

-- | A higher-kinded 'tabulateLogarithm'
ftabulateFLogarithm
  :: FDistributive f => (FLogarithm f ~> a) -> f a
ftabulateFLogarithm
  = \f -> fdistrib (FTab f) $ \(FTab f') -> f' (FLogarithm runF1)
{-# inline ftabulateFLogarithm #-}

-- | A higher-kinded 'indexLogarithm'
findexFLogarithm :: f a -> FLogarithm f ~> a
findexFLogarithm = \fa (FLogarithm k) -> k fa
{-# inline findexFLogarithm #-}

-- | A higher-kinded 'tabulateRep'
ftabulateRep
  :: forall f a.
     (FDistributive (Rep1 f), Generic1 f, Coercible (FLog f) (FLog (Rep1 f)))
  => (FLog f ~> a) -> f a
ftabulateRep = \f -> to1 $ ftabulate (\x -> f (coerce x))
{-# inline ftabulateRep #-}

-- | A higher-kinded 'indexRep'
findexRep
  :: forall f a.
     (FDistributive (Rep1 f), Generic1 f, Coercible (FLog f) (FLog (Rep1 f)))
  => f a -> FLog f ~> a
findexRep = \fa flog -> findex (from1 fa) (coerce flog)
{-# inline findexRep #-}

-- | A higher-kinded 'scatterRep'
fscatterRep
  :: (FDistributive (Rep1 f), Generic1 f, FFunctor w)
  => (w % F1 ~> r) -> (g ~> f) -> w g -> f r
fscatterRep = \k phi -> to1 . fscatter k (from1 . phi)
{-# inline fscatterRep #-}

fscatterDefault
  :: (FDistributive f, FFunctor w)
  => (w % F1 ~> r)
  -> (g ~> f)
  -> w g -> f r
fscatterDefault = \k phi wg ->
  ftabulate $ \x -> k $ ffmap (\g -> F1 $ findex (phi g) x) wg
{-# inline fscatterDefault #-}

-- | A higher-kinded 'Tabulate'
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
  defaultFTabulate :: (FLog f ~> a) -> f a

instance DefaultFImplC 'True f => DefaultFTabulate' 'True f where
  defaultFTabulate = ftabulateFLogarithm
  {-# inline defaultFTabulate #-}

instance DefaultFImplC 'False f => DefaultFTabulate' 'False f where
  defaultFTabulate = ftabulateRep
  {-# inline defaultFTabulate #-}

class DefaultFImplC containsRec1 f => DefaultFIndex' (containsRec1 :: Bool) f where
  defaultFIndex :: f a -> FLog f ~> a

instance DefaultFImplC 'True f => DefaultFIndex' 'True f where
  defaultFIndex = findexFLogarithm
  {-# inline defaultFIndex #-}

instance DefaultFImplC 'False f => DefaultFIndex' 'False f where
  defaultFIndex = findexRep
  {-# inline defaultFIndex #-}

type DefaultFLog f = DefaultFLog' (ContainsSelfRec1 (Rep1 f) 3) f
type DefaultFTabulate f = DefaultFTabulate' (ContainsSelfRec1 (Rep1 f) 3) f
type DefaultFIndex f = DefaultFIndex' (ContainsSelfRec1 (Rep1 f) 3) f

-- | A higher-kinded 'distribute'
--
-- @
-- 'fdistribute' = 'fcollect' 'id'
-- @
fdistribute
  :: (Functor f, FDistributive g)
  => f (g a) -> g (Compose f a)
fdistribute = \f ->
  fdistrib (FCompose f) $ \(FCompose f') ->
    Compose $ fmap coerce f'
{-# inline fdistribute #-}

-- | A higher-kinded 'collect'
--
-- @
-- 'fcollect' f = 'fdistribute' . 'fmap' f
-- @
fcollect
  :: (Functor f, FDistributive g)
  => (a -> g b)
  -> f a -> g (Compose f b)
fcollect = \f fa ->
  fdistrib (FCompose f) $ \(FCompose f') ->
    Compose $ fmap (coerce f') fa
{-# inline fcollect #-}

-- | A higher-kinded 'cotraverse'
--
-- @
-- 'fcotraverse' f = 'fmap' f . 'fdistribute'
-- @
fcotraverse
  :: (Functor f, FDistributive g)
  => (f % a ~> b)
  -> f (g a) -> g b
fcotraverse = \fab fga ->
  fdistrib (FCompose fga) $ \(FCompose f') ->
    fab (fmap coerce f')
{-# inline fcotraverse #-}

instance (FDistributive f, FDistributive g) => FDistributive (f :*: g) where
  type FLog (f :*: g) = FLog f :+: FLog g
  fscatter = \k f (ffmap f -> w) ->
        fscatter k (\(l :*: _) -> l) w
    :*: fscatter k (\(_ :*: r) -> r) w
  ftabulate = \f -> ftabulate (f . L1) :*: ftabulate (f . R1)
  findex = \(f :*: g) -> \case
    L1 x -> findex f x
    R1 y -> findex g y
  {-# inline fscatter #-}
  {-# inline ftabulate #-}
  {-# inline findex #-}

instance FDistributive f => FDistributive (M1 i c f) where
  type FLog (M1 i c f) = FLog f
  fscatter = \k f -> M1 #. fscatter k (unM1 #. f)
  findex = \(M1 f) -> findex f
  ftabulate = \f -> M1 $ ftabulate f
  {-# inline fscatter #-}
  {-# inline ftabulate #-}
  {-# inline findex #-}

instance FDistributive U1 where
  type FLog U1 = V1
  fscatter = \_ _ _ -> U1
  ftabulate = \_ -> U1
  findex = \_ -> \case
  {-# inline fscatter #-}
  {-# inline ftabulate #-}
  {-# inline findex #-}

instance FDistributive f => FDistributive (Rec1 f) where
  type FLog (Rec1 f) = FLog f
  fscatter = \k f -> Rec1 #. fscatter k (unRec1 #. f)
  findex = \(Rec1 f) -> findex f
  ftabulate = \f -> Rec1 $ ftabulate f
  {-# inline fscatter #-}
  {-# inline ftabulate #-}
  {-# inline findex #-}

instance (Distributive f, FDistributive g) => FDistributive (f :.: g) where
  type FLog (f :.: g) = Const (Log f) :*: FLog g
  fscatter = \k phi wg -> Comp1 $
    scatter (fscatter k coerce .# runAppCompose) id $ AppCompose (ffmap phi wg)
  findex = \(Comp1 f) (Const x :*: y) -> findex (index f x) y
  ftabulate = \f -> Comp1 $ tabulate $ \i -> ftabulate $ \j -> f (Const i :*: j)
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

instance FDistributive (F1 a) where
  type FLog (F1 a) = (:~:) a
  fscatter = \k f w -> F1 $ k $ ffmap f w
  findex = \f Refl -> runF1 f
  ftabulate = \f -> F1 (f Refl)
  {-# inline fscatter #-}
  {-# inline findex #-}
  {-# inline ftabulate #-}

instance FDistributive (NT f) where
  type FLog (NT f) = f
  fscatter = fscatterDefault
  ftabulate = NT
  findex = runNT
  {-# inline findex #-}
  {-# inline ftabulate #-}
  {-# inline fscatter #-}

instance FDistributive Limit where
  type FLog Limit = Proxy
  fscatter = \k f w -> Limit $ k $ ffmap (\x -> F1 $ runLimit $ f x) w
  findex f = const $ runLimit f
  ftabulate = \f -> Limit $ f (Proxy)
  {-# inline findex #-}
  {-# inline ftabulate #-}
  {-# inline fscatter #-}

instance FDistributive (F2 a b) where
  type FLog (F2 a b) = FLogarithm (F2 a b)
  findex = findexFLogarithm
  ftabulate = ftabulateFLogarithm
  fscatter = \k f (ffmap f -> w) ->
     F2 (k $ ffmap (\(F2 x _) -> F1 x) w)
        (k $ ffmap (\(F2 _ y) -> F1 y) w)
  {-# inline findex #-}
  {-# inline ftabulate #-}
  {-# inline fscatter #-}

  -- type FLog (D2 a b) = (:~:) a :+: (:~:) b
  -- findex = \(D2 x y) -> \case
  --  L1 Refl -> x
  --  R1 Refl -> y
  -- ftabulate = \f -> D2 (f $ L1 Refl) (f $ R1 Refl)

instance FDistributive (F3 a b c) where
  type FLog (F3 a b c) = FLogarithm (F3 a b c)
  findex = findexFLogarithm
  ftabulate = ftabulateFLogarithm
  fscatter = \k f (ffmap f -> w) ->
     F3 (k $ ffmap (\(F3 x _ _) -> F1 x) w)
        (k $ ffmap (\(F3 _ x _) -> F1 x) w)
        (k $ ffmap (\(F3 _ _ x) -> F1 x) w)
  {-# inline findex #-}
  {-# inline ftabulate #-}
  {-# inline fscatter #-}

instance FDistributive (F4 a b c d) where
  type FLog (F4 a b c d) = FLogarithm (F4 a b c d)
  findex = findexFLogarithm
  ftabulate = ftabulateFLogarithm
  fscatter = \k f (ffmap f -> w) ->
     F4 (k $ ffmap (\(F4 x _ _ _) -> F1 x) w)
        (k $ ffmap (\(F4 _ x _ _) -> F1 x) w)
        (k $ ffmap (\(F4 _ _ x _) -> F1 x) w)
        (k $ ffmap (\(F4 _ _ _ x) -> F1 x) w)
  {-# inline findex #-}
  {-# inline ftabulate #-}
  {-# inline fscatter #-}

instance FDistributive (F5 a b c d e) where
  type FLog (F5 a b c d e) = FLogarithm (F5 a b c d e)
  findex = findexFLogarithm
  ftabulate = ftabulateFLogarithm
  fscatter = \k f (ffmap f -> w) ->
     F5 (k $ ffmap (\(F5 x _ _ _ _) -> F1 x) w)
        (k $ ffmap (\(F5 _ x _ _ _) -> F1 x) w)
        (k $ ffmap (\(F5 _ _ x _ _) -> F1 x) w)
        (k $ ffmap (\(F5 _ _ _ x _) -> F1 x) w)
        (k $ ffmap (\(F5 _ _ _ _ x) -> F1 x) w)
  {-# inline findex #-}
  {-# inline ftabulate #-}
  {-# inline fscatter #-}

instance FDistributive (FBind x y) where
  type FLog (FBind x y) = FLogarithm (FBind x y)
  findex = findexFLogarithm
  ftabulate = ftabulateFLogarithm
  fscatter = \k f (ffmap f -> w) ->
    FBind (      k $ ffmap (\(FBind x _)  -> F1 x     ) w)
          (\a -> k $ ffmap (\(FBind _ fx) -> F1 $ fx a) w)
  {-# inline findex #-}
  {-# inline ftabulate #-}
  {-# inline fscatter #-}

-- | A higher-kinded 'Dist'
type role FDist representational nominal
newtype FDist f a = FDist { runFDist :: f a }
  deriving stock (Data, Generic, Generic1)
  deriving newtype (FFoldable)

instance (FDistributive f, FTraversable f) => FTraversable (FDist f) where
  ftraverse = \f -> fmap FDist . ftraverse f .# runFDist
  {-# inline ftraverse #-}

deriving newtype instance FDistributive f => FDistributive (FDist f)

-- | A default definition for 'ffmap' from 'FFunctor' in terms of 'FDistributive'
ffmapFDist :: FDistributive f => (a ~> b) -> f a -> f b
ffmapFDist = \f -> fscatter (f .# (runF1 . runF1)) id .# F1
{-# inline ffmapFDist #-}

instance FDistributive f => FFunctor (FDist f) where
  ffmap = ffmapFDist
  {-# inline ffmap #-}

instance FDistributive f => FZip (FDist f) where
  fzipWith = fzipWithFDist
  {-# inline fzipWith #-}

-- | A default definition of 'fzipWith' from 'FZip' in terms of 'FDistributive'
fzipWithFDist :: FDistributive f => (forall x. a x -> b x -> c x) -> f a -> f b -> f c
fzipWithFDist = \f m n ->
  fdistrib (F2 m n) $ \(F2 (F1 m') (F1 n')) -> f m' n'
{-# inline fzipWithFDist #-}

instance FDistributive f => FRepeat (FDist f) where
  frepeat = frepeatFDist
  {-# inline frepeat #-}

-- | A default definition of 'frepeat' from 'FRepeat' in terms of 'FDistributive'
frepeatFDist :: FDistributive f => (forall x. a x) -> f a
frepeatFDist = \ax -> fscatter (\x -> runLimit (getConst x)) id (Const (Limit ax))
-- frepeatDist a = fdistrib Proxy $ \_ -> a
{-# inline frepeatFDist #-}

faskFDist :: FDistributive f => f (FLog f)
faskFDist = ftabulate id
{-# noinline[0] faskFDist #-}

ftraceFDist :: FDistributive f => FLog f a -> f g -> g a
ftraceFDist = \x y -> findex y x

-- | We can convert a 'FLogarithm' of a 'FDistributive' 'FFunctor' to any choice
-- of 'FLog', as the two forms are canonically isomorphic.
--
-- @
-- 'findex' f . 'flogFromLogarithm' ≡ 'findexLogarithm' f
-- 'ftabulate' (f . 'flogFromLogarithm') ≡ 'ftabulateLogarithm' f
-- 'flogFromLogarithm' '.' 'flogToLogarithm' ≡ 'id'
-- 'flogToLogarithm' '.' 'flogFromLogarithm' ≡ 'id'
-- @
flogFromFLogarithm :: FDistributive f => FLogarithm f ~> FLog f
flogFromFLogarithm = \(FLogarithm f) -> f faskFDist
{-# inline flogFromFLogarithm #-}

-- | We can convert any 'FLog' to a 'FLogarithm' as the two types are canonically isomorphic.
--
-- @
-- 'findexLogarithm' f . 'flogToLogarithm' ≡ 'findex' f
-- 'ftabulateLogarithm' (f . 'flogToLogarithm') ≡ 'ftabulate' f
-- 'flogFromLogarithm' '.' 'flogToLogarithm' ≡ 'id'
-- 'flogToLogarithm' '.' 'flogFromLogarithm' ≡ 'id'
-- @
flogToFLogarithm :: FDistributive f => FLog f ~> FLogarithm f
flogToFLogarithm = \f -> FLogarithm (ftraceFDist f)
{-# inline flogToFLogarithm #-}

-------------------------------------------------------------------------------
-- HKD
-------------------------------------------------------------------------------

type role HKD representational nominal nominal
newtype HKD (f :: Type -> Type) (x :: i) (a :: i -> Type) = HKD { runHKD :: f (a x) }

mapHKD :: (f (a x) -> g (b x)) -> HKD f x a -> HKD g x b
mapHKD = \f -> HKD #. f .# runHKD
{-# inline mapHKD #-}

type role DHKD representational nominal nominal
newtype DHKD w x f = DHKD { runDHKD :: w (HKD f x) }

type role Atkey representational nominal nominal
data Atkey a i j where
  Atkey :: a -> Atkey a k k

instance FFunctor w => FFunctor (DHKD w x) where
  ffmap f = DHKD #. ffmap (mapHKD f) .# runDHKD
  {-# inline ffmap #-}

instance Functor f => FFunctor (HKD f x) where
  ffmap = \f -> mapHKD (fmap f)
  {-# inline ffmap #-}

instance FunctorWithIndex i f => FFunctorWithIndex (Atkey i x) (HKD f x) where
  ifmap = \f -> mapHKD (imap (f . Atkey))
  {-# inline ifmap #-}

instance Foldable f => FFoldable (HKD f x) where
  ffoldMap = \f -> foldMap f .# runHKD
  {-# inline ffoldMap #-}

instance FoldableWithIndex i f => FFoldableWithIndex (Atkey i x) (HKD f x) where
  iffoldMap = \f -> ifoldMap (f . Atkey) .# runHKD
  {-# inline iffoldMap #-}

instance Traversable f => FTraversable (HKD f x) where
  ftraverse = \f -> fmap HKD . traverse f .# runHKD
  {-# inline ftraverse #-}

instance TraversableWithIndex i f => FTraversableWithIndex (Atkey i x) (HKD f x) where
  iftraverse = \f -> fmap HKD . itraverse (f . Atkey) .# runHKD
  {-# inline iftraverse #-}

instance Applicative f => FZip (HKD f x) where
  fzipWith = \f (HKD fab) -> HKD #. liftA2 f fab .# runHKD
  {-# inline fzipWith #-}

instance Applicative f => FRepeat (HKD f x) where
  frepeat f = HKD $ pure f
  {-# inline frepeat #-}

instance Distributive f => FDistributive (HKD f x) where
  type FLog (HKD f x) = Atkey (Log f) x
  fscatter = \k g w -> HKD $ distrib (DHKD (ffmap g w)) $ k . ffmap coerce .# runDHKD
  {-# inline fscatter #-}
  findex = \(HKD fa) (Atkey lg) -> index fa lg
  {-# inline findex #-}
  ftabulate = \f -> HKD $ tabulate (f . Atkey)
  {-# inline ftabulate #-}

instance Contravariant f => FContravariant (HKD f x) where
  fcontramap = \f -> HKD #. contramap f .# runHKD
  {-# inline fcontramap #-}

instance Divisible f => FSemidivisible (HKD f x) where
  fdivide = \f g -> HKD #. divide (\a -> case f a of (b :*: c) -> (b, c)) (runHKD g) .# runHKD
  {-# inline fdivide #-}

instance Divisible f => FDivisible (HKD f x) where
  fconquer = HKD conquer
  {-# inline fconquer #-}

instance Decidable f => FSemidecidable (HKD f x) where
  fchoose = \f g -> HKD #. choose (\a -> case f a of
    L1 x -> Left x
    R1 y -> Right y) (runHKD g) .# runHKD
  {-# inline fchoose #-}
  flose f = HKD (lose $ \x -> case f x of)
  {-# inline flose #-}

-------------------------------------------------------------------------------
-- LKD
-------------------------------------------------------------------------------

type role LKD representational nominal
newtype LKD f a = LKD { runLKD :: f (Const a) }

instance FFunctor f => Functor (LKD f) where
  fmap = \f -> LKD #. ffmap (Const #. f .# getConst) .# runLKD
  {-# inline fmap #-}

instance FFunctorWithIndex i f => FunctorWithIndex (Some i) (LKD f) where
  imap = \f -> LKD #. ifmap (\i -> Const #. f (Some i) .# getConst) .# runLKD

instance FFoldable f => Foldable (LKD f) where
  foldMap = \f -> ffoldMap (f .# getConst) .# runLKD
  {-# inline foldMap #-}

instance FFoldableWithIndex i f => FoldableWithIndex (Some i) (LKD f) where
  ifoldMap = \f -> iffoldMap (\i -> f (Some i) .# getConst) .# runLKD
  {-# inline ifoldMap #-}

instance FTraversable f => Traversable (LKD f) where
  traverse = \f -> fmap LKD . ftraverse (fmap Const . f .# getConst) .# runLKD
  {-# inline traverse #-}

instance FTraversableWithIndex i f => TraversableWithIndex (Some i) (LKD f) where
  itraverse = \f -> fmap LKD . iftraverse (\i -> fmap Const . f (Some i) .# getConst) .# runLKD
  {-# inline itraverse #-}

instance FContravariant f => Contravariant (LKD f) where
  contramap = \f -> LKD #. fcontramap (Const #. f .# getConst) .# runLKD
  {-# inline contramap #-}

instance FDivisible f => Divisible (LKD f) where
  divide = \f g -> LKD #. fdivide
    (\(Const a) -> case f a of
      (b,c) -> Const b :*: Const c
    )
    (runLKD g) .# runLKD
  {-# inline divide #-}
  conquer = LKD fconquer
  {-# inline conquer #-}

instance FDecidable f => Decidable (LKD f) where
  choose = \f g -> LKD #. fchoose
    (\(Const a) -> case f a of
      Left b -> L1 (Const b)
      Right b -> R1 (Const b)) (runLKD g) .# runLKD
  {-# inline choose #-}

  lose = \f -> LKD $ flose (absurd . f .# getConst)
  {-# inline lose #-}

-- Assumes FRepeat is FApplicative
instance FRepeat f => Applicative (LKD f) where
  (<*>) = \(LKD fab) -> LKD #. fzipWith coerce fab .# runLKD
  {-# inline (<*>) #-}
  pure = \a -> LKD $ frepeat (Const a)
  {-# inline pure #-}

type role DLKD representational nominal
newtype DLKD w f = DLKD { runDLKD :: w (LKD f) }

instance FFunctor w => FFunctor (DLKD w) where
  ffmap = \f -> DLKD #. ffmap (LKD #. f .# runLKD) .# runDLKD
  {-# inline ffmap #-}

instance FDistributive f => Distributive (LKD f) where
  type Log (LKD f) = Some (FLog f)
  scatter = \k g -> LKD . fscatter (Const #. k .  ffmap coerce .# runDLKD) id . DLKD . ffmap g
  {-# inline scatter #-}
  index = \fa (Some lg) -> getConst (findex (runLKD fa) lg)
  {-# inline index #-}
  tabulate = \f -> LKD $ ftabulate (Const #. f . Some)
  {-# inline tabulate #-}

lowerLogarithm :: FLogarithm f x -> Logarithm (LKD f)
lowerLogarithm = \(FLogarithm f) -> Logarithm $ getConst #. f .# runLKD
{-# inline lowerLogarithm #-}

liftLogarithm :: FDistributive f => Logarithm (LKD f) -> Some (FLogarithm f)
liftLogarithm = \(Logarithm f) -> f $ LKD $ ftabulateFLogarithm (Const #. Some)
{-# inline liftLogarithm #-}

instance (FTraversable f, FDistributive f) => Eq (FLogarithm f a) where
  (==) = on (==) lowerLogarithm
  {-# inline (==) #-}

instance (FTraversable f, FDistributive f) => Ord (FLogarithm f a) where
  compare = on compare lowerLogarithm
  {-# inline compare #-}

-- safer than it looks
instance (FTraversable f, FDistributive f) => GEq (FLogarithm f) where
  geq = \x y ->
    if lowerLogarithm x == lowerLogarithm y
    then Just (unsafeCoerce Refl)
    else Nothing
  {-# inline geq #-}

geqFLog :: forall f a b. (FDistributive f, FTraversable f) => FLog f a -> FLog f b -> Maybe (a :~: b)
geqFLog x y = geq (flogFPath @f x) (flogFPath @f y)
{-# inline geqFLog #-}

gcompareFLog :: forall f a b. (FDistributive f, FTraversable f) => FLog f a -> FLog f b -> GOrdering a b
gcompareFLog x y = gcompare (flogFPath @f x) (flogFPath @f y)
{-# inline gcompareFLog #-}

instance (FTraversable f, FDistributive f) => TestEquality (FLogarithm f) where
  testEquality = geq
  {-# inline testEquality #-}

instance (FTraversable f, FDistributive f) => TestCoercion (FLogarithm f) where
  testCoercion = \x y -> repr <$> geq x y
  {-# inline testCoercion #-}

instance (FTraversable f, FDistributive f) => GCompare (FLogarithm f) where
  gcompare = \x y -> case compare (lowerLogarithm x) (lowerLogarithm y) of
    LT -> GLT
    EQ -> unsafeCoerce GEQ
    GT -> GGT
  {-# inline gcompare #-}

flogFPath :: forall f. (FDistributive f, FTraversable f) => FLog f ~> FPath Proxy
flogFPath = findex $ runTrail (ftraverse fend $ frepeatFDist @f Proxy) id
{-# inline flogFPath #-}

type Lens' s a = forall f. Functor f => (a -> f a) -> s -> f s

type role FPath representational nominal
data FPath f a = FPath (f a) Path

instance GEq (FPath f) where
  geq = \(FPath _ x) (FPath _ y) ->
    if x == y
    then Just (unsafeCoerce Refl)
    else Nothing
  {-# inline geq #-}

instance GCompare (FPath f) where
  gcompare = \(FPath _ x) (FPath _ y) -> case compare x y of
    LT -> GLT
    EQ -> unsafeCoerce GEQ
    GT -> GGT
  {-# inline gcompare #-}

fend :: f a -> Trail (FPath f a)
fend a = FPath a <$> end

_flogarithm :: FTraversable t => FLogarithm t a -> Lens' (t f) (f a)
_flogarithm = \(FLogarithm f) a2ga tf ->
  case f $ runTrail (ftraverse fend tf) id of
    FPath a p -> a2ga a <&> \a' -> runEvil (ftraverse (\a'' -> Evil a'' (const (unsafeCoerce a'))) tf) p
{-# inline _flogarithm #-}

_flog :: (FTraversable t, FDistributive t) => FLog t a -> Lens' (t f) (f a)
_flog = \i a2ga tf ->
  case findex (runTrail (ftraverse fend tf) id) i of
    FPath a p -> a2ga a <&> \a' -> runEvil (ftraverse (\a'' -> Evil a'' (const (unsafeCoerce a'))) tf) p
{-# inline _flog #-}

-- | Construct the lens for a logarithm using @'GEq' ('FLog' t)@ instead of with @'FTraversable' t@
_flogGEq :: (FDistributive t, GEq (FLog t)) => FLog t a -> Lens' (t f) (f a)
_flogGEq = \i a2ga fa -> a2ga (findex fa i) <&> \a' -> ifmapFDist (\j a -> case geq i j of
  Just Refl -> a'
  Nothing -> a) fa
{-# inline _flogGEq #-}

instance (FDistributive f, FLog f ~ i) => FFunctorWithIndex i (FDist f) where
  ifmap = ifmapFDist
  {-# inline ifmap #-}

ifmapFDist
  :: forall f a b. FDistributive f
  => (forall x. FLog f x -> a x -> b x) -> f a -> f b
ifmapFDist = \f -> fzipWithFDist f is
  where is = faskFDist :: f (FLog f)
{-# inline ifmapFDist #-}

instance (FDistributive f, FFoldable f, FLog f ~ i) => FFoldableWithIndex i (FDist f) where
  iffoldMap = iffoldMapFDist
  {-# inline iffoldMap #-}

-- | A default definition for 'ifoldMap' from @FoldableWithIndex@ in terms of 'Distributive'
iffoldMapFDist
  :: forall f m a.
     (FDistributive f, FFoldable f, Monoid m)
  => (forall x. FLog f x -> a x -> m) -> f a -> m
iffoldMapFDist = \f -> ffoldMap getConst . ifmapFDist (\i -> Const #. f i)
{-# inline iffoldMapFDist #-}

instance (FDistributive f, FTraversable f, FLog f ~ i) => FTraversableWithIndex i (FDist f) where
  iftraverse = iftraverseFDist
  {-# inline iftraverse #-}

iftraverseFDist
  :: forall f m a b.
     (FDistributive f, FTraversable f, Applicative m)
  => (forall x. FLog f x -> a x -> m (b x)) -> f a -> m (f b)
iftraverseFDist = \f -> ftraverse getCompose . ifmapFDist (\i -> Compose #. f i)
{-# inline iftraverseFDist #-}

instance FDistributive (FConstrained p) where
  type FLog (FConstrained p) = Dict1 p
  fscatter = \k f (ffmap f -> w) -> FConstrained $ k $ ffmap (\(FConstrained x) -> F1 x) w
  ftabulate = \f -> FConstrained $ f Dict1
  findex = \(FConstrained x) Dict1 -> x
