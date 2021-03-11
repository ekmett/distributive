{-# Language TypeOperators #-}
{-# Language Trustworthy #-}
-- |
-- Module      : Data.Distributive.Util
-- Copyright   : (C) 2021 Edward Kmett
-- License     : BSD-style (see the file LICENSE)
--
-- Maintainer  : Edward Kmett <ekmett@gmail.com>
-- Stability   : provisional
-- Portability : non-portable (ghc 8.0+)
module Data.Distributive.Util where

import Data.Coerce
import Data.HKD
import GHC.Generics

(#.) :: Coercible b c => (b -> c) -> (a -> b) -> a -> c
(#.) _ = coerce
{-# inline (#.) #-}

(.#) :: Coercible a b => (b -> c) -> (a -> b) -> a -> c
(.#) f _ = coerce f
{-# inline (.#) #-}

infixr 9 #., .#

newtype DCompose a f g = DCompose { runDCompose :: f (g a) }
instance Functor f => FFunctor (DCompose a f) where
  ffmap f = DCompose #. (fmap f .# runDCompose)
  {-# inline ffmap #-}

newtype AppCompose w g f = AppCompose { runAppCompose :: w (f :.: g) }
instance FFunctor w => FFunctor (AppCompose w g) where
  ffmap f = AppCompose #. ffmap (Comp1 #. f .# unComp1) .# runAppCompose
  {-# inline ffmap #-}

data D2 a b f = D2 (f a) (f b)
instance FFunctor (D2 a b) where
  ffmap f (D2 a b) = D2 (f a) (f b)
  {-# inline ffmap #-}

data D3 a b c f = D3 (f a) (f b) (f c)
instance FFunctor (D3 a b c) where
  ffmap f (D3 a b c) = D3 (f a) (f b) (f c)
  {-# inline ffmap #-}

data D4 a b c d f = D4 (f a) (f b) (f c) (f d)
instance FFunctor (D4 a b c d) where
  ffmap f (D4 a b c d) = D4 (f a) (f b) (f c) (f d)
  {-# inline ffmap #-}

data D5 a b c d e f = D5 (f a) (f b) (f c) (f d) (f e)
instance FFunctor (D5 a b c d e) where
  ffmap f (D5 a b c d e) = D5 (f a) (f b) (f c) (f d) (f e)
  {-# inline ffmap #-}

data DBind x y f = DBind (f x) (x -> f y)
instance FFunctor (DBind x y) where
  ffmap f (DBind l r) = DBind (f l) (f . r)
  {-# inline ffmap #-}

