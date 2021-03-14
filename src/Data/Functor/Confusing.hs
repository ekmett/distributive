{-# LANGUAGE CPP        #-}
{-# LANGUAGE PolyKinds  #-}
{-# LANGUAGE RankNTypes #-}
{-# Language Safe #-}
-- |
-- Csongor Kiss, Matthew Pickering, and Nicolas Wu. 2018. Generic deriving of generic traversals.
-- Proc. ACM Program. Lang. 2, ICFP, Article 85 (July 2018), 30 pages. DOI: https://doi.org/10.1145/3236780
--
-- https://arxiv.org/abs/1805.06798
--
module Data.Functor.Confusing
  ( confusing, LensLike
  , iconfusing, IxLensLike
  , fconfusing, FLensLike
  , liftCurriedYoneda, yap
  , Curried (..), liftCurried, lowerCurried
  , Yoneda (..), liftYoneda, lowerYoneda
  ) where

#ifndef MIN_VERSION_base
#define MIN_VERSION_base(x,y,z) 0
#endif

-------------------------------------------------------------------------------
-- Confusing
-------------------------------------------------------------------------------

type LensLike f s t a b = (a -> f b) -> s -> f t

confusing :: Applicative f => LensLike (Curried (Yoneda f)) s t a b -> LensLike f s t a b
confusing t = \f -> lowerYoneda . lowerCurried . t (liftCurriedYoneda . f)
{-# inline confusing #-}

liftCurriedYoneda :: Applicative f => f a -> Curried (Yoneda f) a
liftCurriedYoneda fa = Curried (`yap` fa)
{-# inline liftCurriedYoneda #-}

yap :: Applicative f => Yoneda f (a -> b) -> f a -> Yoneda f b
yap (Yoneda k) fa = Yoneda (\ab_r -> k (ab_r .) <*> fa)
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
  fmap f (Curried g) = Curried (g . fmap (.f))
  {-# inline fmap #-}

instance Functor f => Applicative (Curried f) where
  pure a = Curried (fmap ($ a))
  {-# inline pure #-}
  Curried mf <*> Curried ma = Curried (ma . mf . fmap (.))
  {-# inline (<*>) #-}

liftCurried :: Applicative f => f a -> Curried f a
liftCurried fa = Curried (<*> fa)

lowerCurried :: Applicative f => Curried f a -> f a
lowerCurried (Curried f) = f (pure id)

-------------------------------------------------------------------------------
-- Yoneda
-------------------------------------------------------------------------------

newtype Yoneda f a = Yoneda { runYoneda :: forall b. (a -> b) -> f b }

liftYoneda :: Functor f => f a -> Yoneda f a
liftYoneda a = Yoneda (\f -> fmap f a)

lowerYoneda :: Yoneda f a -> f a
lowerYoneda (Yoneda f) = f id

instance Functor (Yoneda f) where
  fmap f m = Yoneda (\k -> runYoneda m (k . f))
  {-# inline fmap #-}

instance Applicative f => Applicative (Yoneda f) where
  pure a = Yoneda (\f -> pure (f a))
  {-# inline pure #-}
  Yoneda m <*> Yoneda n = Yoneda (\f -> m (f .) <*> n id)
  {-# inline (<*>) #-}

-- This is modified version of part of @generic-lens@ library.
--
-- Copyright (c) 2018, Csongor Kiss
-- Copyright (C) 2012-16 Edward Kmett, Eric Mertens
-- 
-- All rights reserved.
-- 
-- Redistribution and use in source and binary forms, with or without
-- modification, are permitted provided that the following conditions are met:
-- 
--     * Redistributions of source code must retain the above copyright
--       notice, this list of conditions and the following disclaimer.
-- 
--     * Redistributions in binary form must reproduce the above
--       copyright notice, this list of conditions and the following
--       disclaimer in the documentation and/or other materials provided
--       with the distribution.
-- 
--     * Neither the name of Csongor Kiss nor the names of other
--       contributors may be used to endorse or promote products derived
--       from this software without specific prior written permission.
-- 
-- THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
-- "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
-- LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
-- A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
-- OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
-- SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
-- LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
-- DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
-- THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
-- (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
-- OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
-- 
