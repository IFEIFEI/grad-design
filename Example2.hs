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

newtype Mem = Mem Int deriving (Show)
mapMem :: (Int -> Int) -> Mem -> Mem
mapMem f (Mem x) = Mem (f x)
runMem :: Mem -> Int
runMem (Mem m) = m

data Incr t = Incr Int t
data Recall t = Recall (Int -> t)
data Clear t = Clear t

deriving instance Functor Incr
deriving instance Functor Recall
deriving instance Functor Clear
instance (Show t) => Show (Incr t) where
    show (Incr a t) = "Show Incr " ++ show a ++ show t
instance (Show t) => Show (Recall t) where
    show (Recall r) = "Show Recall Int -> " ++ show (r 1)
instance (Show t) => Show (Clear t) where
    show (Clear t) = "Show Clear " ++ show t

class (Functor sub,Functor sup) => sub :<: sup where
    inj :: sub a -> sup a
instance Functor f => f :<: f where
    inj = id
instance (Functor f, Functor g) => f :<: (f :+: g) where
    inj = L1
instance (Functor f, Functor g, Functor h, f :<: g) => f :<: (h :+: g) where
    inj = R1 . inj

type MemOp =  Incr :+: Recall :+: Clear
instance Show (Free MemOp ()) where
    show a = "Free memop ()"

inject :: (g :<: f) => g (Free f a) -> Free f a
inject = Free . inj

incr :: (Incr :<: f) => Int -> Free f ()
incr i = inject (Incr i (return ()))

recall :: (Recall :<: f) => Free f Int
recall = inject (Recall return)

clear :: (Clear :<: f) => Free f ()
clear = inject (Clear (return ()))

-- newtype StateMem a = StateMem (Mem -> (a, Mem)) deriving (Functor)
-- data MS f t = MS (Int -> Free f (Int -> MS f t))
-- type FreeMS f t = Free f (MS f Int)
--
-- incr :: (Incr :<: f) => FreeMS f t -> Int -> FreeMS f t
-- incr t i = inject (Incr i t)
--
-- recall :: (Recall :<: f) => FreeMS f t -> FreeMS f t
-- recall t = inject (Recall Pure)
--
-- clear :: (Clear :<: f) => Free f () -> Free f ()
-- clear t = inject (Clear (return ()))
--

input :: String
input = "recall; incr 1; clear; incr 1; incr 1; recall; end"

data IncrExpr e = IncrExpr Int e
data RecallExpr e = RecallExpr e
data ClearExpr e = ClearExpr e
data EndExpr e = EndExpr
deriving instance Functor IncrExpr
deriving instance Functor RecallExpr
deriving instance Functor ClearExpr
deriving instance Functor EndExpr
instance (Show t) => Show (IncrExpr t) where
    show (IncrExpr a t) = "Show Incr " ++ show a ++ show t
instance (Show t) => Show (RecallExpr t) where
    show (RecallExpr t) = "Show Recall " ++ show t
instance (Show t) => Show (ClearExpr t) where
    show (ClearExpr t) = "Show Clear " ++ show t
instance (Show t) => Show (EndExpr t) where
    show (EndExpr) = "Show End"
-- instance (Show (f a), Show (g a))  => Show ( (f :+: g) a) where
--     show (L1 f) = show f
--     show (R1 g) = show g

data Expr f = In (f (Expr f))
instance Show (Expr CompExpr) where
    show (In t) = show t
type CompExpr = EndExpr :+: IncrExpr :+: RecallExpr :+: ClearExpr
injectExpr :: (g :<: f) => g (Expr f) -> Expr f
injectExpr = In . inj
incrExpr :: (IncrExpr :<: f) => Int -> Expr f -> Expr f
incrExpr i e = injectExpr $ IncrExpr i e
recallExpr :: (RecallExpr :<: f) => Expr f -> Expr f
recallExpr e = injectExpr $ RecallExpr e
clearExpr :: (ClearExpr :<: f) => Expr f -> Expr f
clearExpr e  = injectExpr $ ClearExpr e
endExpr :: (EndExpr :<: f) => Expr f
endExpr = injectExpr $ EndExpr

memop :: Parser (Expr (EndExpr :+: IncrExpr :+: RecallExpr :+: ClearExpr))
memop = do { symb "clear"; symb ";"; t <- memop; return $ clearExpr t } +++
        do { symb "recall"; symb ";"; t <- memop; return $ recallExpr t } +++
        do { symb "incr"; x <- number; symb ";"; t <- memop; return $ incrExpr x t } +++
        do { symb "end"; return $ endExpr }

number :: Parser Int
number = do { ns <- many1 digit1; return $ foldl (\x y-> x*10 + y) 0 ns}
digit1 = do { x <- token (sat isDigit); return $  (ord x - ord '0')}

foldExpr :: Functor f => (f a -> a) -> Expr f -> a
foldExpr f (In t) = f (fmap (foldExpr f ) t)

class Functor f => Run f where
    runAlgebra :: (Run f0) => f (Expr f0) ->  Free NewMemOp (Either () Int)                     -- 额外增加部分
instance Run IncrExpr where
    runAlgebra (IncrExpr i (In t)) = do { incr i; runAlgebra t}
    -- runAlgebra (IncrExpr i (In t)) = trace "incr_expr" $ do { incr i; runAlgebra t}
instance Run RecallExpr where
    runAlgebra (RecallExpr (In t)) = do { x <- recall; runAlgebra t; return $ Right x}
    -- runAlgebra (RecallExpr (In t)) = trace "recall_expr" $ do { x <- recall; runAlgebra t; return ()}
instance Run ClearExpr where
    runAlgebra (ClearExpr (In t)) = do { clear; runAlgebra t }
    -- runAlgebra (ClearExpr (In t)) = trace "clear_expr" $ do { clear; runAlgebra t }
instance Run EndExpr where
    runAlgebra (EndExpr) = return $ Left ()
    -- runAlgebra (EndExpr) = trace "end_expr" $ return ()
instance (Run f, Run g) => Run (f :+: g) where
    runAlgebra (L1 r) = runAlgebra r
    runAlgebra (R1 r) = runAlgebra r
    -- runAlgebra (L1 r) = trace "L" $ runAlgebra r
    -- runAlgebra (R1 r) = trace "R" $ runAlgebra r

exprx = fst $ (parse memop input)!!0
expr :: CompExpr (Expr CompExpr)
expr = let In t = exprx in t

checkExpr :: Expr CompExpr -> Bool
checkExpr (In (L1 EndExpr)) = False
checkExpr _ = True

whenM :: (Monoid a, Monad m) => Bool -> m a -> m a
whenM x m = if x then m else return mempty
whileM :: (Monoid a, Monad m) => m Bool -> m a -> m a
whileM act m = do {b <- act; whenM b m}


ticki :: Free MemOp Int     -- Pure () | Incr 1 (Free Incr ()) :: Free Incr ()
ticki = do
        y <- recall
        clear
        incr 1
        incr 1
        return y
tickz :: Free MemOp Int     -- Pure () | Incr 1 (Free Incr ()) :: Free Incr ()
tickz = do
        y <- recall
        clear
        z <- recall
        incr 1
        incr 2
        x <- recall
        return y
        return x
tickv :: Free MemOp ()
tickv = do
        clear
        incr 1
        incr 2
-- peekNum :: Free MemOp Int
-- peekNum = do {y <- recall; return y}

-- infixr 6 :@:
-- data (f :: k -> Type) (:@:)  (g :: k -> Type) a = f a :@: a
-- newtype Fix f = In (f (Fix f)) -- 单不动点
-- data Fix f g = FIn (f (Fix f g)) (g (Fix f g))
-- -- data Functor f g => CoIntp f a = CoIntp  (f a)
--  f a :*: g a :*: k a
--  f a :*: r g k a

type CoMemIntp = CoIncr :*: CoRecall :*: CoClear
type LinkCoMemIntp = (CoIncr :*: Incr) :*: (CoRecall :*: Recall) :*: (CoClear :*: Clear)
-- coIncr :: Monad m => m Mem -> Int -> m Mem
-- coIncr m x = do { z <- m ; return $ mapMem (\t -> t + x) z}
-- coRecall :: Monad m => m Mem -> m (Int, Mem)
-- coRecall m = do { x <- m ; return (runMem x, x) }
-- coClear :: Monad m => m Mem -> m Mem
-- coClear _ = return $ Mem 0
coIncr :: Mem -> Int -> Mem
coIncr m x = mapMem (\t -> t + x) m
coRecall :: Mem -> (Int, Mem)
coRecall m = (runMem m, m)
coClear :: Mem -> Mem
coClear _ = Mem 0

interpretMem :: Mem -> Cofree CoMemIntp Mem
interpretMem mem = coiter next start
                    where
                        next s = (CoIncr $ coIncr s) :*: (CoRecall $ coRecall s) :*: (CoClear $ coClear s)
                        start = mem
-- a :< (coiter psi <$> psi a) Free Incr ()


invLProd :: (Functor f, Functor g) => (f :*: g) a -> f a
invLProd (fa :*: _) = fa
invRProd :: (Functor f, Functor g) => (f :*: g) a -> g a
invRProd (_ :*: ga) = ga

instance (Functor f, Functor g) => (f :*: g) :<: f where
    inj = invLProd
instance (Functor f, Functor g, Functor h, g :<: f) => (h :*: g) :<: f  where
    inj = inj . invRProd

type family PairPred (f :: * -> *) (g :: * -> *) :: * where
    PairPred Identity Identity = HTrue
    PairPred ((->) a) ((,) a) = HTrue
    PairPred ((,) a) ((->) a) = HTrue
    PairPred f (g :+: k) = And (CastHTrue (PairPred f g)) (CastHTrue (PairPred f k))
    PairPred (f :*: h) k = Or (CastHTrue (PairPred f k))  (CastHTrue (PairPred h k))
    PairPred (Cofree f) (Free g) = HTrue
    -- type instance PairPred CoIncr Incr = HTrue
    -- type instance PairPred CoRecall Recall = HTrue
    -- type instance PairPred CoClear Clear = HTrue
    PairPred CoIncr Incr = HTrue
    PairPred CoRecall Recall = HTrue
    PairPred CoClear Clear = HTrue
    PairPred CoTick Tick = HTrue
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
    -- pair' _ p (f :*: h) g = trace "Pairing (f :*: [h]) g" $ pair p h g


instance {-# OVERLAPs #-} Pairing' HTrue CoIncr Incr where
    pair' _ f (CoIncr i) (Incr x t) = f (i x) t
instance {-# OVERLAPs #-} Pairing' HTrue CoRecall Recall where
    pair' _ f (CoRecall r) (Recall c) = pair f r c
instance {-# OVERLAPs #-} Pairing' HTrue CoClear Clear where
    pair' _ f (CoClear a) (Clear b) = f a b

-- Add a new tick syntatic
data Tick t = Tick t
deriving instance Functor Tick
type NewMemOp =  Tick :+: MemOp
tick :: (Tick :<: f) => Free f ()
tick = inject $ Tick $ return ()
data TickExpr e = TickExpr e
deriving instance Functor TickExpr
type NewCompExpr = TickExpr :+: CompExpr -- EndExpr :+: IncrExpr :+: RecallExpr :+: ClearExpr :+:
tickExpr :: (TickExpr :<: f) => Expr f -> Expr f
tickExpr e  = injectExpr $ TickExpr e
instance Run TickExpr where
    runAlgebra (TickExpr (In t)) = do { tick; runAlgebra t }
new_memop :: Parser (Expr (NewCompExpr))
new_memop = do { symb "clear"; symb ";"; t <- new_memop; return $ clearExpr t } +++
            do { symb "recall"; symb ";"; t <- new_memop; return $ recallExpr t } +++
            do { symb "incr"; x <- number; symb ";"; t <- new_memop; return $ incrExpr x t } +++
            do { symb "end"; return $ endExpr } +++
            do { symb "tick"; symb ";"; t <- new_memop; return $ tickExpr t }
newtype CoTick a = CoTick a deriving (Functor)
type NewCoMemIntp = CoTick :*: CoMemIntp
newtype CoIncr a = CoIncr (Int -> a) deriving (Functor)
newtype CoRecall a = CoRecall (Int, a) deriving (Functor)
newtype CoClear a = CoClear a deriving (Functor)
coTick :: Mem -> Mem
coTick m = mapMem (\t -> t + 1) m
new_interpretMem :: Mem -> Cofree NewCoMemIntp Mem
new_interpretMem mem = coiter next start
                    where
                        next s = (CoTick $ coTick s) :*: (CoIncr $ coIncr s) :*: (CoRecall $ coRecall s) :*: (CoClear $ coClear s)
                        start = mem
instance {-# OVERLAPs #-} Pairing' HTrue CoTick Tick where
    pair' _ f (CoTick a) (Tick b) = f a b

-- foldTerm :: Functor f => (a -> b) -> (f b -> b) -> Free f a -> b
-- foldTerm pur imp (Pure x) = pur x
-- foldTerm pur imp (Free t) = imp (fmap (foldTerm pur imp) t)
--
-- class Functor f => Run f where
--     runAlgebra :: f (Mem -> (a, Mem)) -> (Mem -> (a, Mem))
--
-- instance Run Incr where
--     runAlgebra (Incr k r) (Mem i) = r (Mem (i+k))
-- instance Run Recall where
--     runAlgebra (Recall r) (Mem i) = r i (Mem i)
-- instance Run Clear where
--     runAlgebra (Clear r) (Mem i) = r (Mem 0)
-- instance (Run f, Run g) => Run (f :+: g) where
--     runAlgebra (L1 r) = runAlgebra r
--     runAlgebra (R1 r) = runAlgebra r
--
-- run :: Run f => Free f a -> Mem -> (a, Mem)
-- run = foldTerm (,) runAlgebra


--
-- t :: Free Recall Int
-- t = recall >>= (\y -> return y)
--     do {y <- recall; return y}

s = Mem 10
c = (CoIncr $ coIncr s)
i = (CoIncr $ coIncr s) :*: (CoRecall $ coRecall s) :*: (CoClear $ coClear s)
lInt = Identity 1 :*: Identity 2
rInt = Identity 3
t = Incr 1 1

-- get the memory value
m = pair const (interpretMem s) ticki
mzv = pair const (interpretMem s) tickz
-- get the recall value
r = pair (flip const) (interpretMem s) ticki
mzr = pair (flip const) (interpretMem s) tickz

mvv = pair const (interpretMem s) tickv
mvr = pair (flip const) (interpretMem s) tickv

e =  runAlgebra expr
mev =  pair const (interpretMem s) e
mer = pair (flip const) (interpretMem s) e

re x = case x of
        Pure _ -> "Pure"
        Free _ -> "Free"

-- tickt test
tickt :: Free NewMemOp Int
tickt = do
        clear
        incr 1
        incr 2
        tick
        v <- recall
        tick
        return v

input1 :: String
input1 = "recall; incr 1; clear; incr 1; incr 1; tick; tick; recall; end"
exprt = fst $ (parse new_memop input1)!!0
expr1 :: NewCompExpr (Expr NewCompExpr)
expr1 = let In t = exprt in t
te = runAlgebra expr1
rt = pair (flip const) (new_interpretMem s) te
mvt = pair const (new_interpretMem s) te



















--
