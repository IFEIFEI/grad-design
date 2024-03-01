{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# language DeriveFunctor #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# language StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# language TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

import Data.Char
import Data.Kind
import Data.Typeable
import Debug.Trace
import GHC.Generics
import Control.Monad
import Control.Monad.Identity
import Control.Monad.Free
import Control.Comonad.Cofree

import Classes
import Combinator
import Components
import TypeLogic

data LightState = LightOn | LightOff deriving (Show)
newtype Light = Light LightState deriving (Show)
switchLight :: Light -> Light
switchLight (Light LightOn) = Light LightOff
switchLight _ = (Light LightOn)
runLight :: Light -> LightState
runLight (Light s) = s

data Switch t = Switch t
data Check t = Check (LightState -> t)

deriving instance Functor Switch
deriving instance Functor Check

class (Functor sub,Functor sup) => sub :<: sup where
  inj :: sub a -> sup a
instance Functor f => f :<: f where
  inj = id
instance (Functor f, Functor g) => f :<: (f :+: g) where
  inj = L1
instance (Functor f, Functor g, Functor h, f :<: g) => f :<: (h :+: g) where
  inj = R1 . inj

type LightOp = Switch :+: Check

inject :: (g :<: f) => g (Free f a) -> Free f a
inject = Free . inj

switch :: (Switch :<: f) => Free f ()
switch = inject (Switch (return ()))

check :: (Check :<: f) => Free f LightState
check = inject (Check return)

newtype CoSwitch a = CoSwitch a deriving (Functor)
newtype CoCheck  a = CoCheck (LightState, a) deriving (Functor)
type CoLightOp = CoSwitch :*: CoCheck

coSwitch :: Light -> Light
coSwitch = switchLight
coCheck :: Light -> (LightState, Light)
coCheck light = (runLight light, light)
intpLight :: Light -> Cofree CoLightOp Light
intpLight light = coiter next start
                    where
                        next s = (CoSwitch $ coSwitch s) :*: (CoCheck $ coCheck s)
                        start = light
type family PairPred (f :: * -> *) (g :: * -> *) :: * where
    PairPred Identity Identity = HTrue
    PairPred ((->) a) ((,) a) = HTrue
    PairPred ((,) a) ((->) a) = HTrue
    PairPred f (g :+: k) = And (CastHTrue (PairPred f g)) (CastHTrue (PairPred f k))
    PairPred (f :*: h) k = Or (CastHTrue (PairPred f k))  (CastHTrue (PairPred h k))
    PairPred (Cofree f) (Free g) = HTrue

    PairPred CoSwitch Switch = HTrue
    PairPred CoCheck Check = HTrue
    PairPred f g = HFalse

class (Functor f, Functor g) => Pairing f g where
    pair :: (a -> b -> r) -> f a -> g b -> r

class (Functor f, Functor g) => Pairing' flag f g where
    pair' :: flag -> (a -> b -> r) -> f a -> g b -> r

instance (Functor f, Functor g, PairPred f g ~ flag, Pairing' flag f g) => Pairing f g where
    pair = pair' (undefined::flag)

instance {-# OVERLAPPABLE #-} (Functor f, Functor g) => Pairing' HFalse f g where
    pair' _ _ _ _ = error "No pair method"
instance {-# OVERLAPs #-} Pairing' HTrue Identity Identity where
    pair' _ f (Identity a) (Identity b) = f a b
    -- pair' _ f (Identity a) (Identity b) = trace "Pairing Identity Identity" f a b
instance {-# OVERLAPs #-} Pairing' HTrue ((->) a) ((,) a) where
    pair' _ p f = uncurry (p . f)
    -- pair' _ p f = trace "Pairing ((->) a) ((,) a)" uncurry (p . f)
instance {-# OVERLAPs #-} Pairing' HTrue ((,) a) ((->) a) where
    pair' _ p f g = pair (flip p) g f
    -- pair' _ p f g =  trace " Pairing ((,) a) ((->) a)" pair (flip p) g f
instance {-# OVERLAPs #-} Pairing f g => Pairing' HTrue (Cofree f) (Free g) where
    pair' _ p (a :< _ ) (Pure x)  = p a x
    pair' _ p (_ :< fs) (Free gs) = pair (pair p) fs gs
    -- pair' _ p (a :< _ ) (Pure x)  = trace "CF PURE" p a x
    -- pair' _ p (_ :< fs) (Free gs) = trace "CF FREE" pair (pair p) fs gs
instance {-# OVERLAPs #-} (Pairing g f, Pairing g h) => Pairing' HTrue g (f :+: h) where
    pair' _ p g (L1 f) = pair p g f
    pair' _ p g (R1 h) = pair p g h
    -- pair' _ p g (L1 f) = trace "Pairing g ([f] :+: g)" $ pair p g f
    -- pair' _ p g (R1 h) = trace "Pairing g (f :+: [g])" $ pair p g h
instance {-# OVERLAPs #-} (Functor h, Or (CastHTrue (PairPred f g)) (PairPred h g) ~ HLTrue, Pairing f g) => Pairing' HLTrue (f :*: h) g where
    pair' _ p (f :*: h) g = pair p f g
    -- pair' _ p (f :*: h) g = trace "Pairing ([f] :*: h) g" $ pair p f g
instance {-# OVERLAPs #-} (Functor f, Or (PairPred f g) (CastHTrue (PairPred h g)) ~ HRTrue, Pairing h g) => Pairing' HRTrue (f :*: h) g where
    pair' _ p (f :*: h) g = pair p h g
instance {-# OVERLAPs #-} Pairing' HTrue CoSwitch Switch where
    pair' _ f (CoSwitch a) (Switch b) = f a b
instance {-# OVERLAPs #-} Pairing' HTrue CoCheck Check where
    pair' _ f (CoCheck r) (Check c) = pair f r c

s0 = Light LightOn
opStream :: Free LightOp LightState
opStream = do
        switch
        v <- check
        switch
        return v
        
rt = pair (flip const) (intpLight s0) opStream
mvt = pair const (intpLight s0) opStream
