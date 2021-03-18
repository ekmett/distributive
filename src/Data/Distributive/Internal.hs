{-# Language BlockArguments #-}
{-# Language DataKinds #-}
{-# Language DeriveFunctor #-}
{-# Language LambdaCase #-}
{-# Language PolyKinds #-}
{-# Language RoleAnnotations #-}
{-# Language Safe #-}
{-# Language TypeFamilies #-}
{-# Language TypeOperators #-}
{-# Language UndecidableInstances #-}

-- |
-- Copyright   : (C) 2021 Edward Kmett
-- License     : BSD-style (see the file LICENSE)
--
-- Maintainer  : Edward Kmett <ekmett@gmail.com>
-- Stability   : provisional
-- Portability : non-portable (ghc 8.0+)

module Data.Distributive.Internal
( (<&>)
, type ContainsSelfRec1
, AppCompose(..)
, Path(..)
, Trail(..)
, end
, Evil(..)
, runEvil
) where

import Data.Distributive.Internal.Coerce
import Data.HKD
import Data.Kind
import Data.Type.Bool (type (||))
import GHC.Generics
import GHC.TypeLits (Nat, type (-))
import Data.Functor

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

type role AppCompose representational nominal nominal
newtype AppCompose w g f = AppCompose { runAppCompose :: w (f :.: g) }
instance FFunctor w => FFunctor (AppCompose w g) where
  ffmap f = AppCompose #. ffmap (Comp1 #. f .# unComp1) .# runAppCompose
  {-# inline ffmap #-}

data Path = End | L Path | R Path deriving (Eq, Ord, Show, Read)

-- This is not a legal 'Applicative', but it is used towards legal ends.

type role Trail representational
newtype Trail a = Trail { runTrail :: (Path -> Path) -> a }
  deriving Functor

instance Applicative Trail where
  pure = Trail . const
  {-# inline pure #-}

  (<*>) = \fab fa -> Trail \k -> runTrail fab (k . L) $ runTrail fa (k . R)
  {-# inline (<*>) #-}

end :: Trail Path
end = Trail \k -> k End
{-# inline end #-}

-- This is also not a legal 'Applicative', but it is used towards legal ends.

type role Evil representational
data Evil a = Evil a (Path -> a)
  deriving Functor

instance Applicative Evil where
  pure = \a -> Evil a \_ -> a
  {-# inline pure #-}
  (<*>) = \ ~(Evil mb mg) ~(Evil nb ng) -> Evil (mb nb) \case
    L xs -> mg xs nb
    R xs -> mb (ng xs)
    End -> undefined
  {-# inline (<*>) #-}

runEvil :: Evil a -> Path -> a
runEvil = \(Evil _ mg) -> mg
{-# inline runEvil #-}
