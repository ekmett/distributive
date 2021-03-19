
module Data.HKD.Variant where

import Data.HKD
import Data.HKD.Record

data Variant (as :: [i]) (f :: i -> Type) where 
    Variant :: {-# unpack #-} !Index as a -> f a -> Variant as f
  deriving anyclass FFunctor, FFoldable

instance FTraversable (Variant as) where

instance FFoldableWithIndex (Index as) 
instance FTraversableWithIndex (Index as) (Variant as) where
  iftraverse f (Variant i as) = Variant <$> f i as

zap :: (forall x. f x -> g x -> r) -> Variant as f -> Record as g -> r
zap k (Variant i f) g = k f (index g i)
