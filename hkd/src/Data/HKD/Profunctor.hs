{-# Language Trustworthy #-}

module Data.HKD.Profunctor
( FProfunctor(fdimap, flmap, frmap)
, FStrong(..)
, FChoice(..)
, FCostrong(..)
, FCochoice(..)
, FStar(..)
, FCostar(..)
) where

import Data.Coerce
-- import Data.Functor.Compose
import Data.HKD.Classes
import Data.HKD.Profunctor.Unsafe
import GHC.Generics

fswap :: (a :*: b) ~> (b :*: a)
fswap (a :*: b) = (b :*: a)
{-# inline fswap #-}

class FProfunctor p => FStrong p where
  ffirst :: p a b -> p (a :*: c) (b :*: c)
  ffirst = fdimap fswap fswap . fsecond
  fsecond :: p a b -> p (c :*: a) (c :*: b)
  fsecond = fdimap fswap fswap . ffirst
  {-# minimal ffirst | fsecond #-}
  {-# inline ffirst #-}
  {-# inline fsecond #-}

fswaps :: (a :+: b) ~> (b :+: a)
fswaps (L1 a) = R1 a
fswaps (R1 b) = L1 b
{-# inline fswaps #-}

{-
flensVL
  :: forall p s t a b. FStrong p 
  => (forall f. Functor f => (forall x. a x -> f (b x)) -> forall y. s y -> f (t y))
  -> p a b -> p s t
flensVL l = fdimap hither yon . ffirst where
  hither :: s x -> (a :*: c) x
  hither = undefined
  yon :: (b :*: c) x -> t x
  yon = undefined

-- (\s -> getCompose $ l (\a -> Compose (a :*: NT id)) s) (\(x :*: y) -> _ y x) . ffirst

-- uncurry (flip id)) . ffirst
{-# inline flensVL #-}
-}

class FProfunctor p => FChoice p where
  fleft :: p a b -> p (a :+: c) (b :+: c) 
  fleft = fdimap fswaps fswaps . fright
  fright :: p a b -> p (c :+: a) (c :+: b)
  fright = fdimap fswaps fswaps . fleft
  {-# minimal fleft | fright #-}
  {-# inline fleft #-}
  {-# inline fright #-}

class FProfunctor p => FCostrong p where
  funfirst :: p (a :*: c) (b :*: c) -> p a b
  funfirst = funsecond . fdimap fswap fswap 
  funsecond :: p (c :*: a) (c :*: b) -> p a b
  funsecond = funfirst . fdimap fswap fswap 
  {-# minimal funfirst | funsecond #-}
  {-# inline funfirst #-}
  {-# inline funsecond #-}

class FProfunctor p => FCochoice p where
  funleft :: p (a :+: c) (b :+: c) -> p a b
  funleft = funright . fdimap fswaps fswaps 
  funright :: p (c :+: a) (c :+: b) -> p a b
  funright = funleft . fdimap fswaps fswaps 
  {-# minimal funleft | funright #-}
  {-# inline funleft #-}
  {-# inline funright #-}

type role FStar representational representational nominal
newtype FStar f a b = FStar { runFStar :: forall x. a x -> f (b x) }

instance Functor f => FProfunctor (FStar f) where
  fdimap = \f g h -> FStar (fmap g . runFStar h . f)
  {-# inline fdimap #-}
  (.##) (p :: FStar f b c) (_ :: a ~> b) = FStar go where
    go :: forall y. Coercible (b y) (a y) => a y -> f (c y)
    go = coerce (runFStar p :: b y -> f (c y))
  {-# inline (.##) #-}
  
instance Functor f => FFunctor (FStar f a) where
  ffmap = \f h -> FStar (fmap f . runFStar h)
  {-# inline ffmap #-}

-- type FCostar :: (Type -> Type) -> (i -> Type) -> (i -> Type) -> Type
type role FCostar representational nominal representational
newtype FCostar f a b = FCostar { runFCostar :: forall x. f (a x) -> b x }

instance Functor f => FProfunctor (FCostar f) where
  fdimap = \f g h -> FCostar (g . runFCostar h . fmap f)
  {-# inline fdimap #-}
  (##.) (_ :: b ~> c) (p :: FCostar f a b) = FCostar go where
    go :: forall y. Coercible (c y) (b y) => f (a y) -> c y
    go = coerce (runFCostar p :: f (a y) -> b y)
  {-# inline (##.) #-}

instance FFunctor (FCostar f a) where
  ffmap = \f h -> FCostar (f . runFCostar h)
  {-# inline ffmap #-}

instance Functor f => FCostrong (FCostar f) where
  funfirst (f :: FCostar f (a :*: c) (b :*: c)) = FCostar f' where
    f' :: forall x. f (a x) -> b x
    f' fa = b where 
      (b :*: d) = runFCostar f ((\a -> (a :*: d)) <$> fa)
  funsecond (f :: FCostar f (c :*: a) (c :*: b)) = FCostar f' where
    f' :: forall x. f (a x) -> b x
    f' fa = b where 
      (d :*: b) = runFCostar f ((:*:) d <$> fa)
  {-# inline funfirst #-}
  {-# inline funsecond #-}
