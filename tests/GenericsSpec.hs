{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE TypeOperators  #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  GenericSpec
-- Copyright   :  (C) 2011-2021 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
--
-- Tests for generically derived 'Distributive' instances.
----------------------------------------------------------------------------
module GenericsSpec (main, spec) where

import Test.Hspec

import Data.Rep
import Data.Type.Equality
import GHC.Generics

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
  describe "Id" $
    it "distribute idExample = idExample" $
      distribute idExample `shouldBe` idExample
  describe "Stream" $
    it "runId (shead (stail (distribute streamExample))) = 1" $
      runId (shead (stail (distribute streamExample))) `shouldBe` 1
  describe "PolyRec" $
    it "runId (plast (runId (pinit (distribute polyRecExample)))) = 1" $
      runId (plast (runId (pinit (distribute polyRecExample)))) `shouldBe` 1

newtype Id a = Id { runId :: a }
  deriving stock (Generic1, Functor, Show)
  deriving newtype Eq
  deriving anyclass (Indexable, Representable)

idExample :: Id (Id Int)
idExample = Id (Id 42)

_logId :: Log Id :~: Fin 1
_logId = Refl

data Stream a = (:>) { shead :: a, stail :: Stream a }
  deriving stock (Generic1, Functor)
  deriving anyclass (Indexable, Representable)

streamExample :: Id (Stream Int)
streamExample = Id $ let s = 0 :> fmap (+1) s in s

_logStream :: Log Stream :~: Logarithm Stream
_logStream = Refl

data PolyRec a = PolyRec { pinit :: Id (PolyRec a), plast :: a }
  deriving stock (Generic1, Functor)
  deriving anyclass (Indexable, Representable)

polyRecExample :: Id (PolyRec Int)
polyRecExample = Id $ let p = PolyRec (Id $ fmap (+1) p) 0 in p

_logPolyRec :: Log PolyRec :~: Logarithm PolyRec
_logPolyRec = Refl

data Id2 a = Id2 (Id a) (Id a)
  deriving stock (Generic1, Functor)
  deriving anyclass (Indexable, Representable)

_logId2 :: Log Id2 :~: Fin 2
_logId2 = Refl
