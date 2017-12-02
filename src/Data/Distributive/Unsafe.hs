{-# language TypeFamilies #-}
module Data.Distributive.Unsafe (unsafeDefaultApply, unsafeDefaultLiftA2) where

import Unsafe.Coerce (unsafeCoerce)
import Data.Distributive

type family Any where

data Two a = Two Any Any
instance Functor Two where
  fmap f (Two a b) = Two (unsafeCoerce f a) (unsafeCoerce f b)

-- | A valid definition of '<*>' or '<.>' for any valid 'Distributive'
-- instance. If the 'Distributive' instance is invalid, be prepared for
-- nasal demons.
unsafeDefaultApply :: Distributive g => g (a -> b) -> g a -> g b
unsafeDefaultApply = unsafeDefaultLiftA2 ($)

-- | A valid definition of 'liftA2' for any valid 'Distributive'
-- instance. If the 'Distributive' instance is invalid, be prepared for
-- nasal demons.
unsafeDefaultLiftA2 :: Distributive g => (a -> b -> c) -> g a -> g b -> g c
unsafeDefaultLiftA2 f xs ys = (\(Two x y) -> unsafeCoerce f x y) <$>
                       distribute (Two (unsafeCoerce xs) (unsafeCoerce ys))
