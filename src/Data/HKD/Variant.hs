{-# Language Safe #-}

module Data.HKD.Variant
( Variant(..)
, zapWith
) where

import Data.HKD
import Data.HKD.Distributive
import Data.HKD.Record
import Data.HKD.WithIndex

data Variant as f where
    Variant :: {-# unpack #-} !(Index as a) -> f a -> Variant as f
  deriving anyclass (FFunctor, FFoldable)

instance FTraversable (Variant as) where
  ftraverse f (Variant i x) = Variant i <$> f x

instance FFunctorWithIndex (Index as) (Variant as)
instance FFoldableWithIndex (Index as) (Variant as)
instance FTraversableWithIndex (Index as) (Variant as) where
  iftraverse f (Variant i x) = Variant i <$> f i x

zapWith :: (forall x. f x -> g x -> r) -> Variant as f -> Record as g -> r
zapWith k (Variant i f) g = k f (findex g i)
{-# inline zapWith #-}
