{-# LANGUAGE Unsafe #-}
module Data.HKD.Profunctor.Unsafe
( FProfunctor(..)
) where

import Data.Coerce
import Data.Kind
import Data.HKD.Classes

class (forall c. FFunctor (p c)) => FProfunctor (p :: (i -> Type) -> (j -> Type) -> Type) where
  fdimap :: (a ~> b) -> (c ~> d) -> p b c -> p a d
  fdimap = \f g -> flmap f . frmap g
  {-# inline fdimap #-}

  flmap :: (a ~> b) -> p b c -> p a c
  flmap = \f -> fdimap f id
  {-# inline flmap #-}

  frmap :: (a ~> b) -> p c a -> p c b
  frmap = fdimap id
  {-# inline frmap #-}

  (##.) :: forall a b c. (forall x. Coercible (c x) (b x)) => (b ~> c) -> p a b -> p a c
  (##.) = \_ -> \p -> p `seq` frmap go p where
     go :: forall y. Coercible (c y) (b y) => b y -> c y
     go = coerce
  {-# inline (##.) #-}

  (.##) :: forall a b c. (forall x. Coercible (b x) (a x)) => p b c -> (a ~> b) -> p a c
  (.##) = \p _ -> p `seq` flmap go p where
    go :: forall y. Coercible (b y) (a y) => a y -> b y
    go = coerce
  {-# inline (.##) #-}

