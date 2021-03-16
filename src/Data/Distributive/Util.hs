{-# Language CPP #-}
{-# Language DataKinds #-}
{-# Language DeriveFunctor #-}
{-# Language DeriveGeneric #-}
{-# Language PatternSynonyms #-}
{-# Language LambdaCase #-}
{-# Language PolyKinds #-}
{-# Language RoleAnnotations #-}
{-# Language Safe #-}
{-# Language TypeFamilies #-}
{-# Language TypeOperators #-}
{-# Language UndecidableInstances #-}
{-# Language ViewPatterns #-}

#ifndef MIN_VERSION_base
#define MIN_VERSION_base(_x,_y,_z) 1
#endif

-- |
-- Module      : Data.Distributive.Util
-- Copyright   : (C) 2021 Edward Kmett
-- License     : BSD-style (see the file LICENSE)
--
-- Maintainer  : Edward Kmett <ekmett@gmail.com>
-- Stability   : provisional
-- Portability : non-portable (ghc 8.0+)

module Data.Distributive.Util
( (<&>)
, type ContainsSelfRec1
, DCompose(..)
, D2(..)
, D3(..)
, D4(..)
, D5(..)
, DBind(..)
, Path(..)
, Trail(..)
, end
, Evil(..)
, runEvil
) where

import Data.Distributive.Coerce
import Data.HKD
import Data.Kind
import Data.Type.Bool (type (||))
import GHC.Generics
import GHC.TypeLits (Nat, type (-))
#if MIN_VERSION_base(4,11,0)
import Data.Functor
#else
(<&>) :: Functor f => f a -> (a -> b) -> f b
m <&> f = fmap f m
infixl 1 <&>
#endif

-- Does Generic Rep contain 'Rec1'?
--
-- This is a Hack. If we loop i (= 3) times we declared we are recursive.
type family ContainsSelfRec1 (f :: j -> Type) (i :: Nat) :: Bool where
  ContainsSelfRec1 _          0 = 'True
  ContainsSelfRec1 (K1 _ _)   i = 'False
  ContainsSelfRec1 (M1 _ _ f) i = ContainsSelfRec1 f i
  ContainsSelfRec1 U1         i = 'False
  ContainsSelfRec1 V1         i = 'False
  ContainsSelfRec1 Par1       _ = 'False
  ContainsSelfRec1 (f :*: g)  i = ContainsSelfRec1 f i || ContainsSelfRec1 g i
  ContainsSelfRec1 (f :+: g)  i = ContainsSelfRec1 f i || ContainsSelfRec1 g i
  ContainsSelfRec1 (f :.: g)  i = ContainsSelfRec1 f i || ContainsSelfRec1 g i

  -- this clause is a hack. If pieces @f@ is built from are not 'Generic1',
  -- this will get stuck.
  --
  -- An alternative with non-linear match is suboptimal in other ways
  ContainsSelfRec1 (Rec1 f)   i = ContainsSelfRec1 (Rep1 f) (i - 1)

type role DCompose nominal representational nominal
newtype DCompose a f g = DCompose { runDCompose :: f (g a) }
instance Functor f => FFunctor (DCompose a f) where
  ffmap f = DCompose #. (fmap f .# runDCompose)
  {-# inline ffmap #-}

type role D2 nominal nominal representational
data D2 a b f = D2 (f a) (f b)
instance FFunctor (D2 a b) where
  ffmap f (D2 a b) = D2 (f a) (f b)
  {-# inline ffmap #-}

type role D3 nominal nominal nominal representational
data D3 a b c f = D3 (f a) (f b) (f c)
instance FFunctor (D3 a b c) where
  ffmap f (D3 a b c) = D3 (f a) (f b) (f c)
  {-# inline ffmap #-}

type role D4 nominal nominal nominal nominal representational
data D4 a b c d f = D4 (f a) (f b) (f c) (f d)
instance FFunctor (D4 a b c d) where
  ffmap f (D4 a b c d) = D4 (f a) (f b) (f c) (f d)
  {-# inline ffmap #-}

type role D5 nominal nominal nominal nominal nominal representational
data D5 a b c d e f = D5 (f a) (f b) (f c) (f d) (f e)
instance FFunctor (D5 a b c d e) where
  ffmap f (D5 a b c d e) = D5 (f a) (f b) (f c) (f d) (f e)
  {-# inline ffmap #-}

type role DBind nominal nominal representational
data DBind x y f = DBind (f x) (x -> f y)
instance FFunctor (DBind x y) where
  ffmap f (DBind l r) = DBind (f l) (f . r)
  {-# inline ffmap #-}

data Path = End | L Path | R Path deriving (Eq, Ord, Show, Read)

-- This is not a legal 'Applicative', but it is used towards legal ends.

type role Trail representational
newtype Trail a = Trail { runTrail :: (Path -> Path) -> a }
  deriving Functor

instance Applicative Trail where
  pure = Trail . const
  {-# inline pure #-}

  fab <*> fa = Trail $ \k -> runTrail fab (k . L) $ runTrail fa (k . R)
  {-# inline (<*>) #-}

end :: Trail Path
end = Trail $ \k -> k End
{-# inline end #-}

-- This is also not a legal 'Applicative', but it is used towards legal ends.

type role Evil representational
data Evil a = Evil a (Path -> a)
  deriving Functor

instance Applicative Evil where
  pure a = Evil a $ \_ -> a
  {-# inline pure #-}
  ~(Evil mb mg) <*> ~(Evil nb ng) = Evil (mb nb) $ \case
    L xs -> mg xs nb
    R xs -> mb (ng xs)
    End -> undefined
  {-# inline (<*>) #-}

runEvil :: Evil a -> Path -> a
runEvil (Evil _ mg) p = mg p
{-# inline runEvil #-}
