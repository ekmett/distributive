{-# Language CPP #-}
{-# Language GeneralizedNewtypeDeriving #-}
{-# Language Unsafe #-}
{-# options_haddock hide #-}

module Data.Distributive.Internal.Vec
( Vec(UnsafeVec,Vec,toVector)
, pattern V
, FromVector(..)
, withDim
) where

import Control.Monad
import Control.Monad.Reader.Class
import Control.Monad.Fix
import Control.Monad.Zip
import Data.Distributive
import Data.Distributive.Internal.Coerce
import Data.Distributive.Internal.Fin
import Data.Foldable.WithIndex
import Data.Functor.Classes
import Data.Functor.Identity
import Data.Functor.WithIndex
import Data.HKD
import Data.Proxy
import Data.Traversable.WithIndex
import Data.Type.Equality
import Data.Vector as V
import GHC.Exts
import GHC.TypeNats
import Unsafe.Coerce
import Text.Read

type role Vec nominal representational
newtype Vec (n :: Nat) a = UnsafeVec (Vector a)
  deriving stock (Functor, Foldable, Traversable)
  deriving newtype (Eq, Eq1, Ord, Ord1, Show, Show1)

pattern Vec :: Vector a -> Vec n a
pattern Vec { toVector } <- UnsafeVec toVector

{-# complete Vec :: Vec #-}

instance Indexable (Vec n) where
  type Log (Vec n) = Fin n
  type KnownSize (Vec n) = 'Just n

  index :: forall a. Vec n a -> Fin n -> a
  index = coerce ((!) :: Vector a -> Int -> a)
  {-# inline index #-}

instance KnownNat n => Distributive (Vec n) where
  scatter = \(k :: w Identity -> r) f (ffmap f -> w) -> UnsafeVec $
    generate (int @n) \i -> k $ ffmap (\v -> Identity $ index v $ UnsafeFin i) w
  {-# inlinable scatter #-}

  tabulate = \(f :: Fin n -> a) -> UnsafeVec $ generate (int @n) (f .# UnsafeFin)
  {-# inlinable tabulate #-}


instance (KnownNat n, Read a) => Read (Vec n a) where
  readPrec = do
    l <- step readPrec 
    let v = V.fromList l
    UnsafeVec v <$ guard (V.length v == int @n)

instance KnownNat n => Read1 (Vec n) where
  liftReadPrec _ rl = do
    l <- rl
    let v = V.fromList l
    UnsafeVec v <$ guard (V.length v == int @n)
  {-# inline liftReadPrec #-}

instance FunctorWithIndex (Fin n) (Vec n) where
  imap :: forall a b. (Fin n -> a -> b) -> Vec n a -> Vec n b
  imap = coerce (V.imap :: (Int -> a -> b) -> Vector a -> Vector b)
  {-# inline imap #-}

instance FoldableWithIndex (Fin n) (Vec n) where
  ifoldMap f = V.ifoldr (\i a b -> f (UnsafeFin i) a `mappend` b) mempty .# toVector
  {-# inline ifoldMap #-}

instance TraversableWithIndex (Fin n) (Vec n) where
  itraverse f (toVector -> as) = UnsafeVec #. V.fromListN (V.length as) <$>
    itraverse (f .# UnsafeFin) (V.toList as)
  {-# inline itraverse #-}

data SomeVec a where
  SomeVec :: KnownNat n => Vec n a -> SomeVec a

asVec :: FromVector t a => t -> SomeVec a
asVec (UnsafeVec #. asVector -> v) = withDim v (SomeVec v)
{-# inline asVec #-}

withDim :: forall n a r. Vec n a -> (KnownNat n => r) -> r
withDim v r = case someNatVal (fromIntegral $ V.length (toVector v)) of
  SomeNat (Proxy :: Proxy n') -> case unsafeCoerce Refl of
    (Refl :: n :~: n') -> r
{-# inline withDim #-}

class FromVector t a | t -> a where
  asVector :: t -> Vector a
  vectorAs :: Vector a -> t

instance FromVector (Vector a) a where
  asVector = id
  vectorAs = id

instance FromVector [a] a where
  asVector = V.fromList
  vectorAs = V.toList

pattern V :: FromVector t a => KnownNat n => Vec n a -> t
pattern V v <- (asVec -> SomeVec v) where
  V v = vectorAs (toVector v)

{-# complete V :: Vector #-}
{-# complete V :: [] #-}

deriving via Dist (Vec n) instance KnownNat n => Applicative (Vec n)
deriving via Dist (Vec n) instance KnownNat n => Monad (Vec n)
deriving via Dist (Vec n) instance KnownNat n => MonadFix (Vec n)
deriving via Dist (Vec n) instance KnownNat n => MonadZip (Vec n)
deriving via Dist (Vec n) instance KnownNat n => MonadReader (Fin n) (Vec n)
deriving via Dist (Vec n) a instance (KnownNat n, Num a) => Num (Vec n a)
deriving via Dist (Vec n) a instance (KnownNat n, Fractional a) => Fractional (Vec n a)
deriving via Dist (Vec n) a instance (KnownNat n, Floating a) => Floating (Vec n a)
