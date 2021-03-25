{-# Language GeneralizedNewtypeDeriving #-}
{-# language Trustworthy #-}

-- |
-- Copyright :  (c) 2019-2021 Edward Kmett
--              (c) 2019 Oleg Grenrus
--              (c) 2017-2021 Aaron Vargo
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable
--
-- "Higher-Kinded Data" such as it is
--
-- Simple usage:
--
-- @
-- data Record f = Record
--   { fieldInt    :: f Int
--   , fieldString :: f String
--   , fieldSome   :: 'Some' f
--   } deriving ('Generic1', 'FFunctor', 'FFoldable', 'FTraversable')
-- @
--
-- Generically derived 'FApply' and 'FApplicative':
--
-- @
-- data Record f = Record
--   { fieldInt    :: f Int
--   , fieldString :: f String
--   } deriving ('Generic1', 'FApply', 'FApplicative')
-- @
module Data.HKD
(
-- * "Natural" transformations
  type (~>)
-- * Functor
, FFunctor(..)
, gffmap
-- * Foldable
, FFoldable(..)
, gffoldMap
, flength
, ftraverse_
, ffor_
-- * Traversable
, FTraversable(..)
, ViaFTraversable(..)
, ffmapDefault
, ffoldMapDefault
, ffor
, fsequence
, FFunctorWithIndex(..)
, ifmapDefault
, FFoldableWithIndex(..)
, iffoldMapDefault
, FTraversableWithIndex(..)
, FApply(..)
, FApplicative(..)
, ViaFApplicative(..)
-- * FBind
, Coatkey(..)
, runCoatkey
, FBind(..)
, ViaFBind(..)
, FMonad
, ViaFMonad(..)
, fbindInner
, fbindOuter
-- * FEq
, EqC, FEq
-- * FOrd
, OrdC', OrdC, FOrd
-- * Higher kinded data
-- | See also "Data.Some" in @some@ package. This package provides instances for it.
, F0(..)
, F1(..)
, F2(F2,..)
, F3(F3,..)
, F4(F4,..)
, F5(F5,..)
, FConstrained(..)
, FCompose(FCompose,runFCompose,..)
, NT(..)
, Lim(..), traverseLim
, Dict1(..)
, Dicts(Dicts,runDicts,..)
, Atkey(..)
, HKD(..), mapHKD
, LKD(..)
) where

import Control.Applicative
import Data.Coerce
import Data.Data
import Data.Functor.Compose (Compose (..))
import Data.Functor.Contravariant
import Data.Functor.Contravariant.Divisible
import Data.Function.Coerce
import Data.HKD.Classes
import Data.HKD.Contravariant
import Data.HKD.Index.Internal
import Data.Functor.WithIndex
import Data.Foldable.WithIndex
import Data.Traversable.WithIndex
import Data.Kind
import Data.Some.Newtype (Some(..))
import Data.Void
import GHC.Arr
import GHC.Generics
import Unsafe.Coerce

type role F0 phantom
data F0 f = F0
  deriving stock
  ( Generic, Generic1, Functor, Foldable, Traversable
  , Eq, Ord, Show, Read, Ix, Enum, Bounded, Data)
  deriving anyclass
  ( FFunctor, FFoldable, FTraversable
  , FFunctorWithIndex (Index '[]), FFoldableWithIndex (Index '[])
  , FContravariant
  , FApplicative, FApply )

instance FTraversableWithIndex (Index '[]) F0 where
  iftraverse _ F0 = pure F0
  {-# inline iftraverse #-}

-- * F1

type role F1 nominal representational
newtype F1 a f = F1 { runF1 :: f a }
  deriving stock (Eq, Ord, Show, Read, Data)
  deriving anyclass
  ( FFunctor
  , FFunctorWithIndex (Index '[a])
  , FFoldableWithIndex (Index '[a])
  )

instance FTraversableWithIndex (Index '[a]) (F1 a) where
  iftraverse f (F1 a) = F1 <$> f (UnsafeIndex 0) a
  {-# inline iftraverse #-}

deriving newtype instance Ix (f a) => Ix (F1 a f)
deriving newtype instance Enum (f a) => Enum (F1 a f)
deriving newtype instance Bounded (f a) => Bounded (F1 a f)

instance FFoldable (F1 a) where
  flengthAcc acc _ = acc + 1
  {-# inline flengthAcc #-}

instance FTraversable (F1 a) where
  ftraverse f = fmap F1 . f .# runF1
  {-# inline ftraverse #-}

instance FApplicative (F1 a) where
  fpure = \ x -> F1 x
  {-# inline fpure #-}

instance FApply (F1 a) where
  fliftA2 = \ f (F1 a) (F1 b) -> F1 (f a b)
  {-# inline fliftA2 #-}

instance FBind (F1 a) where
  fbind = \(F1 a) f -> F1 $ runCoatkey $ runF1 $ f a
  {-# inline fbind #-}

type role F2 nominal nominal representational
data F2 a b f = F2' (F1 a f) (F1 b f)
  deriving stock (Eq, Ord, Show, Read, Generic, Generic1, Data)
  deriving anyclass
  ( FFunctor, FFoldable, FTraversable, FApply, FApplicative
  , FFunctorWithIndex (Index '[a,b])
  , FFoldableWithIndex (Index '[a,b])
  )

pattern F2 :: f a -> f b -> F2 a b f
pattern F2 a b = F2' (F1 a) (F1 b)
{-# complete F2 :: F2 #-}

instance FTraversableWithIndex (Index '[a,b]) (F2 a b) where
  iftraverse f (F2 a b) = liftA2 F2
    (f (UnsafeIndex 0) a)
    (f (UnsafeIndex 1) b)
  {-# inline iftraverse #-}

instance FBind (F2 a b) where
  fbind = \(F2 a b) f ->
    F2
      (runCoatkey $ case f a of F2 x _ -> x)
      (runCoatkey $ case f b of F2 _ y -> y)
  {-# inline fbind #-}

type role F3 nominal nominal nominal representational
data F3 a b c f = F3' (F1 a f) (F1 b f) (F1 c f)
  deriving stock (Eq, Ord, Show, Read, Generic, Generic1, Data)
  deriving anyclass
  ( FFunctor, FFoldable, FTraversable, FApply, FApplicative
  , FFunctorWithIndex (Index '[a,b,c])
  , FFoldableWithIndex (Index '[a,b,c])
  )

pattern F3 :: f a -> f b -> f c -> F3 a b c f
pattern F3 a b c = F3' (F1 a) (F1 b) (F1 c)
{-# complete F3 :: F3 #-}

instance FTraversableWithIndex (Index '[a,b,c]) (F3 a b c) where
  iftraverse f (F3 a b c) = liftA3 F3
    (f (UnsafeIndex 0) a)
    (f (UnsafeIndex 1) b)
    (f (UnsafeIndex 2) c)
  {-# inline iftraverse #-}

instance FBind (F3 a b c) where
  fbind = \(F3 a b c) f ->
    F3
      (runCoatkey $ case f a of F3 x _ _ -> x)
      (runCoatkey $ case f b of F3 _ y _ -> y)
      (runCoatkey $ case f c of F3 _ _ z -> z)
  {-# inline fbind #-}

type role F4 nominal nominal nominal nominal representational
data F4 a b c d f = F4' (F1 a f) (F1 b f) (F1 c f) (F1 d f)
  deriving stock (Eq, Ord, Show, Read, Generic, Generic1, Data)
  deriving anyclass
  ( FFunctor, FFoldable, FTraversable, FApply, FApplicative
  , FFunctorWithIndex (Index '[a,b,c,d])
  , FFoldableWithIndex (Index '[a,b,c,d])
  )

pattern F4 :: f a -> f b -> f c -> f d -> F4 a b c d f
pattern F4 a b c d = F4' (F1 a) (F1 b) (F1 c) (F1 d)
{-# complete F4 :: F4 #-}

instance FTraversableWithIndex (Index '[a,b,c,d]) (F4 a b c d) where
  iftraverse f (F4 a b c d) = liftA2 F4
       (f (UnsafeIndex 0) a)
       (f (UnsafeIndex 1) b)
    <*> f (UnsafeIndex 2) c
    <*> f (UnsafeIndex 3) d
  {-# inline iftraverse #-}

instance FBind (F4 a b c d) where
  fbind = \(F4 a b c d) f ->
    F4
      (runCoatkey $ case f a of F4 x _ _ _ -> x)
      (runCoatkey $ case f b of F4 _ x _ _ -> x)
      (runCoatkey $ case f c of F4 _ _ x _ -> x)
      (runCoatkey $ case f d of F4 _ _ _ x -> x)
  {-# inline fbind #-}

type role F5 nominal nominal nominal nominal nominal representational
data F5 a b c d e f = F5' (F1 a f) (F1 b f) (F1 c f) (F1 d f) (F1 e f)
  deriving stock (Eq, Ord, Show, Read, Generic, Generic1, Data)
  deriving anyclass
  ( FFunctor, FFoldable, FTraversable, FApply, FApplicative
  , FFunctorWithIndex (Index '[a,b,c,d,e])
  , FFoldableWithIndex (Index '[a,b,c,d,e])
  )

pattern F5 :: f a -> f b -> f c -> f d -> f e -> F5 a b c d e f
pattern F5 a b c d e = F5' (F1 a) (F1 b) (F1 c) (F1 d) (F1 e)
{-# complete F5 :: F5 #-}

instance FTraversableWithIndex (Index '[a,b,c,d,e]) (F5 a b c d e) where
  iftraverse f (F5 a b c d e) = liftA2 F5
       (f (UnsafeIndex 0) a)
       (f (UnsafeIndex 1) b)
    <*> f (UnsafeIndex 2) c
    <*> f (UnsafeIndex 3) d
    <*> f (UnsafeIndex 4) e
  {-# inline iftraverse #-}

instance FBind (F5 a b c d e) where
  fbind = \(F5 a b c d e) f ->
    F5
      (runCoatkey $ case f a of F5 x _ _ _ _ -> x)
      (runCoatkey $ case f b of F5 _ x _ _ _ -> x)
      (runCoatkey $ case f c of F5 _ _ x _ _ -> x)
      (runCoatkey $ case f d of F5 _ _ _ x _ -> x)
      (runCoatkey $ case f e of F5 _ _ _ _ x -> x)
  {-# inline fbind #-}

-------------------------------------------------------------------------------
-- "natural" transformations via parametricity
-------------------------------------------------------------------------------

-- | Newtyped "natural" transformation
newtype NT f g = NT { runNT :: f ~> g }


instance FFunctor (NT f) where
  ffmap = \f (NT g) -> NT (f . g)
  {-# inline ffmap #-}

instance FApply (NT f) where
  fliftA2 = \f (NT g) (NT h) -> NT \x -> f (g x) (h x)
  {-# inline fliftA2 #-}

instance FApplicative (NT a) where
  fpure = \x -> NT \_ -> x
  {-# inline fpure #-}

instance FBind (NT r) where
  fbind = \(NT ra) f -> NT \r -> runCoatkey $ runNT (f $ ra r) r
  {-# inline fbind #-}

instance FFunctorWithIndex f (NT f) where
  ifmap f (NT g) = NT $ \r -> f r (g r)
  {-# inline ifmap #-}

-------------------------------------------------------------------------------
-- Lim
-------------------------------------------------------------------------------

newtype Lim f = Lim
  { runLim :: forall a. f a
  }

unsafeLim :: f a -> Lim f
unsafeLim = unsafeCoerce
{-# inline unsafeLim #-}

traverseLim :: forall f g. Traversable f => Lim (Compose f g) -> f (Lim g)
traverseLim (Lim (Compose xs)) = fmap unsafeLim xs
{-# inline traverseLim #-}

deriving stock instance (forall a. Eq (f a)) => Eq (Lim f)
deriving stock instance (forall a. Ord (f a)) => Ord (Lim f)
deriving stock instance (forall a. Show (f a)) => Show (Lim f)
deriving stock instance (forall a. Bounded (f a)) => Bounded (Lim f)

instance (forall a. Enum (f a)) => Enum (Lim f) where
  toEnum x = Lim (toEnum x)
  {-# inline toEnum #-}
  fromEnum (Lim x) = fromEnum x
  {-# inline fromEnum #-}
  succ x = Lim (succ $ runLim x)
  {-# inline succ #-}
  pred x = Lim (pred $ runLim x)
  {-# inline pred #-}
  enumFrom (Lim x) = unsafeLim <$> enumFrom x
  {-# inline enumFrom #-}
  enumFromTo (Lim x) (Lim y) = unsafeLim <$> enumFromTo x y
  {-# inline enumFromTo #-}
  enumFromThen (Lim x) (Lim y) = unsafeLim <$> enumFromThen x y
  {-# inline enumFromThen #-}
  enumFromThenTo (Lim x) (Lim y) (Lim z) = unsafeLim <$> enumFromThenTo x y z
  {-# inline enumFromThenTo #-}

instance (forall a. Ix (f a)) => Ix (Lim f) where
  -- this can be implemented in quadratic time without unsafeCoerce
  range (Lim a, Lim b) = unsafeLim <$> range (a, b)
  {-# inline range #-}
  index (Lim a, Lim b) (Lim c) = index (a, b) c
  {-# inline index #-}
  unsafeIndex (Lim a, Lim b) (Lim c) = unsafeIndex (a, b) c
  {-# inline unsafeIndex #-}
  inRange (Lim a, Lim b) (Lim c) = inRange (a, b) c
  {-# inline inRange #-}
  rangeSize (Lim a, Lim b) = rangeSize (a, b)
  {-# inline rangeSize #-}
  unsafeRangeSize (Lim a, Lim b) = unsafeRangeSize (a, b)
  {-# inline unsafeRangeSize #-}

instance FFunctor Lim where
  ffmap f (Lim g) = Lim (f g)
  {-# inline ffmap #-}

instance FFoldable Lim where
  ffoldMap f (Lim g) = f g
  flengthAcc l _ = l + 1
  {-# inline ffoldMap #-}
  {-# inline flengthAcc #-}

instance FTraversable Lim where
  ftraverse = \ f (Lim m) -> unsafeLim <$> f m
  {-# inline ftraverse #-}

instance FApply Lim where
  fliftA2 f (Lim x) (Lim y) = Lim (f x y)
  {-# inline fliftA2 #-}

instance FApplicative Lim where
  fpure x = Lim x
  {-# inline fpure #-}

instance FBind Lim where
  fbind = \(Lim a) f -> Lim $ runCoatkey $ runLim $ f a
  {-# inline fbind #-}

-- * Dicts

data Dict1 p a where
    Dict1 :: p a => Dict1 p a

deriving stock instance (Typeable k, Typeable a, Typeable p, p a) => Data (Dict1 p (a :: k))
deriving stock instance Eq (Dict1 p a)
deriving stock instance Ord (Dict1 p a)
deriving stock instance Show (Dict1 p a)
deriving stock instance p a => Read (Dict1 p a)

instance p a => Enum (Dict1 p a) where
  succ = error "Dict1.succ"
  pred = error "Dict1.pred"
  toEnum 0 = Dict1
  toEnum _ = error "Dict1.toEnum"
  fromEnum Dict1 = 0
  enumFrom Dict1 = [Dict1]
  enumFromTo Dict1 Dict1 = [Dict1]
  enumFromThen Dict1 Dict1 = repeat Dict1
  enumFromThenTo Dict1 Dict1 Dict1 = repeat Dict1

deriving stock instance p a => Bounded (Dict1 p a)
deriving stock instance Ix (Dict1 p a)

newtype Dicts p f = Dicts'
  { runDicts' :: F1 (Dict1 p) f
  }
  deriving stock (Generic, Generic1)
  deriving anyclass (FFunctor, FFoldable, FTraversable, FApply, FApplicative)

pattern Dicts :: f (Dict1 p) -> Dicts p f
pattern Dicts { runDicts } = Dicts' (F1 runDicts)

{-# complete Dicts #-}

deriving newtype instance Eq (f (Dict1 p)) => Eq (Dicts p f)
deriving newtype instance Ord (f (Dict1 p)) => Ord (Dicts p f)

instance FBind (Dicts p) where
  fbind = \(Dicts a) f -> Dicts $ runCoatkey $ runDicts (f a)
  {-# inline fbind #-}

-- * FConstrained

newtype FConstrained p f = FConstrained
  { runFConstrained :: forall x. p x => f x
  }

{-
instance
  ( Typeable k
  , Typeable p
  , Typeable f
  , forall x. p x => Data (f x)
  ) => Data (FConstrained (p :: k -> Constraint) f) where

  toConstr _ = conFConstrained
  dataTypeOf _ = tyFConstrained
  gunfold k z c = case constrIndex c of
    1 -> k (z FConstrained) -- need some way to sneak into c here

tyFConstrained :: DataType
tyFConstrained = mkDataType "Data.HKD.FConstrained" [conFConstrained]
{-# noinline tyFConstrained #-}

conFConstrained :: Constr
conFConstrained = mkConstr tyFConstrained "C1" [] Data.Data.Prefix
{-# noinline conFConstrained #-}
-}

instance FFunctor (FConstrained p) where
  ffmap = \f x -> FConstrained (f $ runFConstrained x)
  {-# inline ffmap #-}

instance (forall x. p x) => FFoldable (FConstrained p) where
  ffoldMap = \ f x -> f $ runFConstrained x
  {-# inline ffoldMap #-}

instance FApply (FConstrained p) where
  fliftA2 = \f g h -> FConstrained $ f (runFConstrained g) (runFConstrained h)
  {-# inline fliftA2 #-}

instance FApplicative (FConstrained p) where
  fpure x = FConstrained x
  {-# inline fpure #-}

instance FBind (FConstrained p) where
  fbind = \(FConstrained a) f -> FConstrained $ runCoatkey $ runFConstrained $ f a
  {-# inline fbind #-}

-- instance (forall x. p x) => FTraversable (FConstrained p) where

type role FCompose nominal representational nominal
newtype FCompose a f g = FCompose' { runFCompose' :: f (F1 a g) }
  deriving stock (Generic, Generic1)

deriving stock instance Eq (f (F1 a g)) => Eq (FCompose a f g)
deriving stock instance Ord (f (F1 a g)) => Ord (FCompose a f g)
deriving stock instance Show (f (F1 a g)) => Show (FCompose a f g)
deriving stock instance Read (f (F1 a g)) => Read (FCompose a f g)

pattern FCompose :: Functor f => f (g a) -> FCompose a f g 
pattern FCompose { runFCompose } <- FCompose' (fmap runF1 -> runFCompose) where
  FCompose f = FCompose' (fmap F1 f)

deriving stock instance
  ( Typeable k
  , Typeable a
  , Typeable f
  , Typeable g
  , Data (f (F1 a g))
  ) => Data (FCompose (a :: k) f g)

instance Functor f => FFunctor (FCompose a f) where
  ffmap = \f -> FCompose' #. (fmap (F1 #. f .# runF1) .# runFCompose')
  {-# inline ffmap #-}

instance Foldable f => FFoldable (FCompose a f) where
  ffoldMap = \f -> foldMap (f .# runF1) .# runFCompose'
  {-# inline ffoldMap #-}

instance Traversable f => FTraversable (FCompose a f) where
  ftraverse = \f -> fmap FCompose' . traverse (fmap F1 . f .# runF1) .# runFCompose'
  {-# inline ftraverse #-}

type role HKD representational nominal nominal
newtype HKD (f :: Type -> Type) (x :: i) (a :: i -> Type) = HKD { runHKD :: f (F1 x a) }

mapHKD :: (f (F1 x a) -> g (F1 x b)) -> HKD f x a -> HKD g x b
mapHKD = \f -> HKD #. f .# runHKD
{-# inline mapHKD #-}

type role Atkey representational nominal nominal
data Atkey a i j where
  Atkey :: a -> Atkey a k k

-- if HKD took x as its first parameter i could use FCompose
type role DHKD representational nominal nominal
newtype DHKD w x f = DHKD { runDHKD :: w (HKD f x) }
instance FFunctor w => FFunctor (DHKD w x) where
  ffmap f = DHKD #. ffmap (mapHKD f) .# runDHKD
  {-# inline ffmap #-}

instance Functor f => FFunctor (HKD f x) where
  ffmap = \f -> mapHKD (fmap (F1 #. f .# runF1))
  {-# inline ffmap #-}

instance FunctorWithIndex i f => FFunctorWithIndex (Atkey i x) (HKD f x) where
  ifmap = \f -> mapHKD (imap (\i -> F1 #. f (Atkey i) .# runF1))
  {-# inline ifmap #-}

instance Foldable f => FFoldable (HKD f x) where
  ffoldMap = \f -> foldMap (f .# runF1) .# runHKD
  {-# inline ffoldMap #-}

instance FoldableWithIndex i f => FFoldableWithIndex (Atkey i x) (HKD f x) where
  iffoldMap = \f -> ifoldMap (\i -> f (Atkey i) .# runF1) .# runHKD
  {-# inline iffoldMap #-}

instance Traversable f => FTraversable (HKD f x) where
  ftraverse = \f -> fmap HKD . traverse (fmap F1 . f .# runF1) .# runHKD
  {-# inline ftraverse #-}

instance TraversableWithIndex i f => FTraversableWithIndex (Atkey i x) (HKD f x) where
  iftraverse = \f -> fmap HKD . itraverse (\i -> fmap F1 . f (Atkey i) .# runF1) .# runHKD
  {-# inline iftraverse #-}

instance Applicative f => FApply (HKD f x) where
  fliftA2 = \f (HKD fab) -> HKD #. liftA2 (\(F1 i) (F1 j) -> F1 $ f i j) fab .# runHKD
  {-# inline fliftA2 #-}

instance Applicative f => FApplicative (HKD f x) where
  fpure f = HKD $ pure (F1 f)
  {-# inline fpure #-}

instance Monad f => FBind (HKD f x) where
  fbind = \(HKD fa) f -> HKD $ fmap (F1 #. runCoatkey .# runF1) $ fa >>= runHKD #. f .# runF1
  {-# inline fbind #-}

instance Contravariant f => FContravariant (HKD f x) where
  fcontramap = \f -> HKD #. contramap (F1 #. f .# runF1) .# runHKD
  {-# inline fcontramap #-}

instance Divisible f => FSemidivisible (HKD f x) where
  fdivide = \f g -> HKD #. divide (\(F1 a) -> case f a of (b :*: c) -> (F1 b, F1 c)) (runHKD g) .# runHKD
  {-# inline fdivide #-}

instance Divisible f => FDivisible (HKD f x) where
  fconquer = HKD conquer
  {-# inline fconquer #-}

instance Decidable f => FSemidecidable (HKD f x) where
  fchoose = \f g -> HKD #. choose (\(F1 a) -> case f a of
    L1 x -> Left (F1 x)
    R1 y -> Right (F1 y)) (runHKD g) .# runHKD
  {-# inline fchoose #-}
  flose f = HKD (lose \(F1 x) -> case f x of)
  {-# inline flose #-}

-- LKD

type role LKD representational nominal
newtype LKD f a = LKD { runLKD :: f (Const a) }

deriving stock instance
  ( Typeable f
  , Typeable a
  , Typeable k
  , Data (f (Const a))
  ) => Data (LKD (f :: (k -> Type) -> Type) a)

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

instance FApplicative f => Applicative (LKD f) where
  (<*>) = \(LKD fab) -> LKD #. fliftA2 coerce fab .# runLKD
  {-# inline (<*>) #-}
  pure = \a -> LKD $ fpure (Const a)
  {-# inline pure #-}



instance FMonad f => Monad (LKD f) where
  (>>=) = \(LKD fa) f -> LKD $ fbindOuter fa \(Const a) -> ffmap coerce $ runLKD $ f a
  {-#inline (>>=) #-}

