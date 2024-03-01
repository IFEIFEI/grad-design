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
import Data.Functor.Contravariant
import Debug.Trace
import GHC.Generics
import Control.Monad
import Control.Monad.Free
import Control.Monad.Identity
import Control.Comonad.Cofree


import Classes
import Combinator
import Components
import TypeLogic

{-
expr ::= expr addop term | term
term ::= term mulop factor | factor
factor ::= digit | (expr)
digit ::= 0 | 1 | ... | 9
addop ::= + | -
mulop ::= * | /
-}
data Lit e  = Lit Int           deriving(Eq, Functor, Show)
data Add e  = Add e e           deriving(Eq, Functor, Show)
data Mul e  = Mul e e           deriving(Eq, Functor, Show)
data Minus e    = Minus  e e    deriving(Eq, Functor, Show)
data Divide e   = Divide e e    deriving(Eq, Functor, Show)

class (Functor sub,Functor sup) => sub :<: sup where
    inj :: sub a -> sup a
instance Functor f => f :<: f where
    inj = id
instance (Functor f, Functor g) => f :<: (f :+: g) where
    inj = L1
instance (Functor f, Functor g, Functor h, f :<: g) => f :<: (h :+: g) where
    inj = R1 . inj

inject :: (g :<: f) => g (Free f a) -> Free f a
inject = Free . inj

lit :: (Lit :<: f) => Int -> Free f ()
lit i = inject $ Lit i

add :: (Add :<: f) => Free f () -> Free f () -> Free f ()
add e1 e2 = inject $ Add e1 e2

mul :: (Mul :<: f) => Free f () -> Free f () -> Free f ()
mul e1 e2 = inject $ Mul e1 e2

minus :: (Minus :<: f) => Free f () -> Free f () -> Free f ()
minus e1 e2 = inject $ Minus e1 e2

divide :: (Divide :<: f) => Free f () -> Free f () -> Free f ()
divide e1 e2 = inject $ Divide e1 e2

type Expr =  Lit :+: Add :+: Mul :+: Minus :+: Divide


-- -- expr ::= expr addop term | term
expr :: Parser (Free Expr ())
expr =
    do {a <- term; rest a}
        where
            rest a = (do f <- addop
                         b <- term
                         rest $  (f a b)) +++ return a

-- -- term ::= term mulop factor | factor
term :: Parser (Free Expr ())
term =
     do {a <- factor; rest a}
        where
            rest a = (do f <- mulop
                         b <- term
                         rest $  (f a b)) +++ return a

 -- factor ::= digit | (expr)
factor = number +++ do {symb "("; n <- expr; symb ")"; return n }
-- -- digit ::= 0 | 1 | ... | 9
number :: Parser (Free Expr ())
number = do { ns <- many1 digit1; return $ lit (foldl (\x y-> x*10 + y) 0 ns)}
digit1 = do { x <- token (sat isDigit); return $  (ord x - ord '0')}
-- -- addop ::= + | -
-- -- mulop ::= * | /
addop = do {symb "+"; return (add)} +++ do {symb "-"; return (minus)}
mulop = do {symb "*"; return (mul)} +++ do {symb "/"; return (divide)}

applyExpr :: String -> Parser (Free Expr ()) -> Free Expr ()
applyExpr expr p = fst $ (parse p expr)!!0

expression :: Free Expr ()
expression = fst $ (parse expr "2 + 12 * 3")!!0

foldExpr :: Functor f => (a -> b) -> (f b -> b) -> Free f a -> b
foldExpr pur imp (Pure x) = pur x
foldExpr pur imp (Free t) = imp (fmap (foldExpr pur imp) t)

class Functor f => Run f where
    runAlgebra :: f Int -> Int

instance Run Lit where
    runAlgebra (Lit i) = i
instance Run Add where
    runAlgebra (Add r1 r2) = r1 + r2 -- (r1 a) + (r2 a)
instance Run Mul where
    runAlgebra (Mul r1 r2)  = r1 * r2 -- (r1 a) * (r2 a)
instance Run Minus where
    runAlgebra (Minus r1 r2)  = r1 - r2 -- (r1 a) * (r2 a)
instance Run Divide where
    runAlgebra (Divide r1 r2)  = r1 `div` r2 -- (r1 a) `div` (r2 a)
instance (Run f, Run g) => Run (f :+: g) where
    runAlgebra (L1 r) = runAlgebra r
    runAlgebra (R1 r) = runAlgebra r

run :: Run f => Free f a -> Int
run = foldExpr (const 0) runAlgebra

-- data CoLit e  = CoLit Int deriving(Eq, Functor, Show)
-- data CoAdd e  = CoAdd e e deriving(Eq, Functor, Show)
-- data CoMul e  = CoMul e e deriving(Eq, Functor, Show)
-- data CoMinus e    = CoMinus  e e deriving(Eq, Functor, Show)
-- data CoDivide e   = CoDivide e e deriving(Eq, Functor, Show)
--
--
-- type family PairPred (f :: * -> *) (g :: * -> *) :: * where
--     PairPred Identity Identity = HTrue
--     PairPred ((->) a) ((,) a) = HTrue
--     PairPred ((,) a) ((->) a) = HTrue
--     PairPred f (g :+: k) = And (CastHTrue (PairPred f g)) (CastHTrue (PairPred f k))
--     PairPred (f :*: h) k = Or (CastHTrue (PairPred f k))  (CastHTrue (PairPred h k))
--     PairPred (Cofree f) (Free g) = HTrue
--     PairPred CoLit Lit = HTrue
--     PairPred CoAdd Add = HTrue
--     PairPred CoMul Mul = HTrue
--     PairPred CoMinus Minus = HTrue
--     PairPred CoDivide Divide = HTrue
--     PairPred f g = HFalse
--
-- class (Functor f, Functor g) => Pairing f g where
--     pair :: (a -> b -> r) -> (r -> r -> r) -> f a -> g b -> r
-- class (Functor f, Functor g) => Pairing' flag f g where
--     pair' :: flag -> (a -> b -> r) -> (r -> r -> r) -> f a -> g b -> r
-- instance (Functor f, Functor g, PairPred f g ~ flag, Pairing' flag f g) => Pairing f g where
--     pair = pair' (undefined::flag)
-- instance {-# OVERLAPPABLE #-} (Functor f, Functor g) => Pairing' HFalse f g where
--     pair' _ _ _ _ = error "No pair method"
-- instance {-# OVERLAPs #-} Pairing' HTrue Identity Identity where
--     pair' _ f _ (Identity a) (Identity b) = trace "Pairing Identity Identity" f a b
-- instance {-# OVERLAPs #-} Pairing' HTrue ((->) a) ((,) a) where
--     pair' _ p _ f = trace "Pairing ((->) a) ((,) a)" uncurry (p . f)
-- instance {-# OVERLAPs #-} Pairing' HTrue ((,) a) ((->) a) where
--     pair' _ p r f g =  trace " Pairing ((->) a) ((,) a)" pair (flip p) r g f
-- instance {-# OVERLAPs #-} Pairing f g => Pairing' HTrue (Cofree f) (Free g) where
--     pair' _ p _ (a :< _ ) (Pure x)  = trace "CF PURE" p a x
--     pair' _ p r (_ :< fs) (Free gs) = trace "CF FREE" pair (pair p r) r fs gs
-- instance {-# OVERLAPs #-} (Pairing g f, Pairing g h) => Pairing' HTrue g (f :+: h) where
--     pair' _ p r g (L1 f) = trace "Pairing g ([f] :+: g)" $ pair p r g f
--     pair' _ p r g (R1 h) = trace "Pairing g (f :+: [g])" $ pair p r g h
-- instance {-# OVERLAPs #-} (Functor h, Or (PairPred f g) (PairPred h g) ~ HLTrue, Pairing f g) => Pairing' HLTrue (f :*: h) g where
--     pair' _ p r (f :*: h) g = trace "Pairing ([f] :*: h) g" $ pair p r f g
-- instance {-# OVERLAPs #-} (Functor f, Or (PairPred f g) (PairPred h g) ~ HRTrue, Pairing h g) => Pairing' HRTrue (f :*: h) g where
--     pair' _ p r (f :*: h) g = trace "Pairing (f :*: [h]) g" $ pair p r h g

-- instance {-# OVERLAPs #-} Pairing' HTrue CoLit Lit where
--     pair' _ f _ (CoLit i) (Lit x t) = f (i x)
-- instance {-# OVERLAPs #-} Pairing' HTrue CoAdd Add where
--     pair' _ f r (CoAdd ce1 ce2) (Add e1 e2) = r (f ce1 e2) (f e1 e2)
-- instance {-# OVERLAPs #-} Pairing' HTrue CoMul Mul where
--     pair' _ f r (CoMul ce1 ce2) (Mul e1 e2) = r (f ce1 e2) (f e1 e2)
-- instance {-# OVERLAPs #-} Pairing' HTrue CoMinus Minus where
--     pair' _ f r (CoMinus ce1 ce2) (Minus e1 e2) = r (f ce1 e2) (f e1 e2)
-- instance {-# OVERLAPs #-} Pairing' HTrue CoDivide Divide where
--     pair' _ f r (CoDivide ce1 ce2) (Divide e1 e2) = r (f ce1 e2) (f e1 e2)
--
-- type CoExpr =  CoLit :*: CoAdd :*: CoMul :*: CoMinus :*: CoDivide









































-- expr :: Parser (Fix ExprF)
-- expr =
--     do {a <- term; rest a}
--         where
--             rest a = (do f <- addop
--                          b <- term
--                          rest $ In (f a b)) +++ return a
-- term =
--     do {a <- factor; rest a}
--         where
--             rest a = (do f <- mulop
--                          b <- term
--                          rest $ In (f a b)) +++ return a
-- factor = number +++ do {symb "("; n <- expr; symb ")"; return n }
-- number = do { ns <- many1 digit1; return $ In (Number (foldl (\x y-> x*10 + y) 0 ns))}
-- digit1 = do { x <- token (sat isDigit); return $  (ord x - ord '0')}
--
-- addop = do {symb "+"; return (Add)} +++ do {symb "-"; return (Minus)}
-- mulop = do {symb "*"; return (Mul)} +++ do {symb "/"; return (Divide)}
--
