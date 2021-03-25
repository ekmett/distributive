{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
#if __GLASGOW_HASKELL__ <800
{-# LANGUAGE UndecidableInstances #-}
#endif
module Main where

#if MIN_VERSION_base(4,9,0)
import Data.Kind (Type)
#else
#define Type *
#endif

import Data.HKD
import Control.Applicative as A (Applicative (pure), liftA2)
import Data.Monoid as Mon (Monoid (..))

-- We can define flipped NP (as in sop-code), which would be instance
-- of classes in Data.HKD

data NP (xs :: [k]) (f :: k -> Type) where
    Nil  :: NP '[] f
    (:*) :: f x -> NP xs f -> NP (x ': xs) f

instance FFunctor (NP xs) where
    ffmap _ Nil       = Nil
    ffmap f (x :* xs) = f x :* ffmap f xs

instance FFoldable (NP xs) where
    ffoldMap _ Nil       = Mon.mempty
    ffoldMap f (x :* xs) = mappend (f x) (ffoldMap f xs)

    flengthAcc !acc Nil       = acc
    flengthAcc !acc (_ :* xs) = flengthAcc acc xs

instance FTraversable (NP xs) where
    ftraverse _ Nil       = A.pure Nil
    ftraverse f (x :* xs) = liftA2 (:*) (f x) (ftraverse f xs)

-------------------------------------------------------------------------------
-- Apply
-------------------------------------------------------------------------------

class FFunctor t => FApply t where
    fliftA2 :: (forall x. f x -> g x -> h x) -> t f -> t g -> t h

instance FApply (NP xs)  where
    fliftA2 _ Nil       Nil       = Nil
    fliftA2 f (x :* xs) (y :* ys) = f x y :* fliftA2 f xs ys

instance FApply (Element a) where
    fliftA2 f (Element x) (Element y) = Element (f x y)

instance FApply (NT f) where
    fliftA2 f (NT g) (NT h) = NT $ \x -> f (g x) (h x)

instance FApply Limit where
    fliftA2 f (Limit x) (Limit y) = Limit (f x y)

-------------------------------------------------------------------------------
-- Applicative
-------------------------------------------------------------------------------

class FApply t => FApplicative t where
    fpure :: (forall x. f x) -> t f

instance FApplicativeNP xs => FApplicative (NP xs) where
    fpure = fpureNP

class FApplicativeNP xs where
    fpureNP :: (forall x. f x) -> NP xs f

instance FApplicativeNP '[] where
    fpureNP _ = Nil

instance FApplicativeNP xs => FApplicativeNP (x ': xs) where
    fpureNP x = x :* fpureNP x

instance FApplicative (Element a) where
    fpure x = Element x

instance FApplicative (NT f) where
    fpure x = NT $ \_ -> x

instance FApplicative Limit where
    fpure x = Limit x

-------------------------------------------------------------------------------
-- Dicts, or what should be a better name?
-------------------------------------------------------------------------------

-- | Dfferent dictionary, not the same as in @constraints@
data Dict c a where
    Dict :: c a => Dict c a

-- | TODO: what should be the superclass?
class FFunctor t => Dicts c t where
    dicts :: t (Dict c)

instance DictsNP c xs => Dicts c (NP xs) where
    dicts = dictsNP

class DictsNP c xs where
    dictsNP :: NP xs (Dict c)

instance DictsNP c '[] where
    dictsNP = Nil

instance (c x, DictsNP c xs) => DictsNP c (x ': xs) where
    dictsNP = Dict :* dictsNP

instance c x => Dicts c (Element x) where
    dicts = Element Dict

-------------------------------------------------------------------------------
-- Main
-------------------------------------------------------------------------------

main :: IO ()
main = return ()
