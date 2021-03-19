{-# Language Safe #-}

-- |
-- Copyright   : (C) 2013-2016 Edward Kmett, Eric Mertens
-- License     : BSD-2-Clause OR Apache-2.0
-- Maintainer  : Edward Kmett <ekmett@gmail.com>
-- Stability   : provisional
-- Portability : non-portable
--
-- This code is derived from Eric Mertens' implementation of the @confusing@ 
-- combinator in @lens@. A description was later published in
--
-- Csongor Kiss, Matthew Pickering, and Nicolas Wu. 2018. <https://arxiv.org/abs/1805.06798 Generic deriving of generic traversals>.
-- Proc. ACM Program. Lang. 2, ICFP, Article 85 (July 2018), 30 pages. DOI: https://doi.org/10.1145/3236780

module Data.Traversable.Confusing
( confusing, LensLike
, iconfusing, IxLensLike
, fconfusing, FLensLike
, liftCurriedYoneda, yap
, Curried (..), liftCurried, lowerCurried
, Yoneda (..), liftYoneda, lowerYoneda
) where

-------------------------------------------------------------------------------
-- Confusing
-------------------------------------------------------------------------------

type LensLike f s t a b = (a -> f b) -> s -> f t

-- | "Fuse" a 'Traversal' by reassociating all of the @('<*>')@ operations to the
-- left and fusing all of the 'fmap' calls into one. This is particularly
-- useful when constructing a 'Traversal' using operations from "GHC.Generics".
--
-- Given a pair of 'Traversal's 'foo' and 'bar',
--
-- @
-- 'confusing' (foo.bar) = foo.bar
-- @
--
-- However, @foo@ and @bar@ are each going to use the 'Applicative' they are given.
--
-- 'confusing' exploits the 'Yoneda' lemma to merge their separate uses of 'fmap' into a single 'fmap'.
-- and it further exploits an interesting property of the right Kan lift (or 'Curried') to left associate
-- all of the uses of @('<*>')@ to make it possible to fuse together more fmaps.
--
-- This is particularly effective when the choice of functor 'f' is unknown at compile
-- time or when the 'Traversal' @foo.bar@ in the above description is recursive or complex
-- enough to prevent inlining.
--
-- 'Control.Lens.Lens.fusing' is a version of this combinator suitable for fusing lenses.
--
-- @
-- 'confusing' :: 'Traversal' s t a b -> 'Traversal' s t a b
-- @
confusing :: Applicative f => LensLike (Curried (Yoneda f)) s t a b -> LensLike f s t a b
confusing t = \f -> lowerYoneda . lowerCurried . t (liftCurriedYoneda . f)
{-# inline confusing #-}

liftCurriedYoneda :: Applicative f => f a -> Curried (Yoneda f) a
liftCurriedYoneda = \fa -> Curried (`yap` fa)
{-# inline liftCurriedYoneda #-}

yap :: Applicative f => Yoneda f (a -> b) -> f a -> Yoneda f b
yap = \(Yoneda k) fa -> Yoneda (\ab_r -> k (ab_r .) <*> fa)
{-# inline yap #-}

type IxLensLike f i s t a b = (i -> a -> f b) -> s -> f t

iconfusing :: Applicative f => IxLensLike (Curried (Yoneda f)) i s t a b -> IxLensLike f i s t a b
iconfusing t = \f -> lowerYoneda . lowerCurried . t (\i a -> liftCurriedYoneda (f i a))
{-# inline iconfusing #-}

type FLensLike f s t a b = (forall x. a x -> f (b x)) -> s -> f t

fconfusing :: Applicative f => FLensLike (Curried (Yoneda f)) s t a b -> FLensLike f s t a b
fconfusing t = \f -> lowerYoneda . lowerCurried . t (liftCurriedYoneda . f)
{-# inline fconfusing #-}

-------------------------------------------------------------------------------
-- Curried
-------------------------------------------------------------------------------

newtype Curried f a = Curried { runCurried :: forall r. f (a -> r) -> f r }

instance Functor f => Functor (Curried f) where
  fmap f = \(Curried g) -> Curried (g . fmap (.f))
  {-# inline fmap #-}

instance Functor f => Applicative (Curried f) where
  pure = \a -> Curried (fmap ($ a))
  {-# inline pure #-}
  (<*>) = \(Curried mf) (Curried ma) -> Curried (ma . mf . fmap (.))
  {-# inline (<*>) #-}

liftCurried :: Applicative f => f a -> Curried f a
liftCurried = \fa -> Curried (<*> fa)
{-# inline liftCurried #-}

lowerCurried :: Applicative f => Curried f a -> f a
lowerCurried = \(Curried f) -> f (pure id)
{-# inline lowerCurried #-}

-------------------------------------------------------------------------------
-- Yoneda
-------------------------------------------------------------------------------

newtype Yoneda f a = Yoneda { runYoneda :: forall b. (a -> b) -> f b }

liftYoneda :: Functor f => f a -> Yoneda f a
liftYoneda = \a -> Yoneda (\f -> fmap f a)
{-# inline liftYoneda #-}

lowerYoneda :: Yoneda f a -> f a
lowerYoneda = \(Yoneda f) -> f id
{-# inline lowerYoneda #-}

instance Functor (Yoneda f) where
  fmap f = \ m -> Yoneda (\k -> runYoneda m (k . f))
  {-# inline fmap #-}

instance Applicative f => Applicative (Yoneda f) where
  pure = \ a -> Yoneda (\f -> pure (f a))
  {-# inline pure #-}
  (<*>) = \ (Yoneda m) (Yoneda n) -> Yoneda (\f -> m (f .) <*> n id)
  {-# inline (<*>) #-}

