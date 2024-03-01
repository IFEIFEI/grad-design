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

data Expr f = In (f (Expr f))




data Para =
    Para_Reg Int                    -- r0
  | Para_Imm Int                    -- #123
  | Para_RegList [Para]             -- {fp, lr}
  | Para_RegBase Para Int Bool      -- [Para, Int]!?

data Push t = Push Para t
data Pop  t = Pop  Para t
data Add  t = Add  Para Para Para t
data Sub  t = Sub  Para Para Para t
data Mov  t = Mov  Para Para t

endtoline :: Parser String
endtoline = do { cs <- many $ satp (\ch -> ch /= '\n') item; char '\n'; return cs}

comment :: Parser String
comment = do { space; symb "@"; endtoline }

input :: String
input = "enqueue:\n\t@ args = 0, pretend = 0, frame = 16\n\t@ frame_needed = 1, uses_anonymous_args = 0\n\tpush\t{fp, lr}\n\tadd\tfp, sp, #4\n\tsub\tsp, sp, #16"

func_def :: Parser String
func_def = do
            name <- symb "enqueue"
            symb ":"
            return name

label :: Parser String
label = do { char '.'; char 'L'; num_list <- many digit; return num_list}

p_reg :: Parser String
p_reg = (do { char 'r'; r1 <- digit; r2 <- digit; return ['r', r1, r2]}) +++ 
        (do { char 'r' ; r1 <- digit; return ['r', r1]}) +++ 
        (symb "fp") +++
        (symb "lr") +++
        (symb "sp") +++ 
        label

p_reglist :: Parser String
p_reglist = do { char '{'; plist <- sepby p_reg (char ',' ); char '}'; return $ concat plist }

param :: Parser String
param = arith_expr +++
        p_reg +++
        p_reglist +++
        do {symb "#-"; imm <- many digit; return imm } +++
        do {char '#';  imm <- many digit; return imm } +++
        do {char '[';  plist <- param_list; char ']'; return $ concat plist} +++
        endtoline
        -- +++
        -- arith_expr

arith_expr :: Parser String
arith_expr = do {p1 <- label; symb "+"; num <- many digit; return $ p1 ++ num}

param_list :: Parser [String]
param_list = sepby param (char ',') 

ipush :: Parser String
ipush = do
          space
          iname <- symb "push"
          reg_list <- p_reglist
          return $ iname ++ " " ++ reg_list

ipop :: Parser String
ipop = do
          space
          iname <- symb "pop"
          reg_list <- p_reglist
          return $ iname ++ " " ++ reg_list

iname_list :: [String]
iname_list = ["push", "add", "sub", "mov", "ldrb", "str", "ldr", "mul", "lsl", "cmp", "bne",
              "b", "pop"]

inst_list :: Parser String
inst_list = p +++ lp +++ world
                where 
                    p = foldr (+++) (symb "nop") p_list
                    p_list = map (\s -> symb s) iname_list
                    lp = do { lname <- label; char ':'; return lname}
                    world = do {space; symb ".word"; endtoline }
            


inst :: Parser String
inst = do { space; name <- inst_list; space; plist <- param_list; return $ name ++ (concat plist) }

test_parser :: Parser String
test_parser = func_def <&> comment <&> comment <&> do {k <- many (comment +++ inst); return $ concat k}

label_input = "\n.L4:\n\tldr\tr2, [fp, #-20]\n\tlsl\tr2, r2, #2\n\tldr\tr1, [fp, #-12]\n\tadd\tr2, r1, r2\n\tldr\tr2, [r2]\n\tstr\tr3, [r2, #232]\n\tldr\tr2, [fp, #-20]\n\tlsl\tr2, r2, #2\n\tldr\tr1, [fp, #-12]\n\tadd\tr2, r1, r2"

lp :: Parser String
lp = do { char '\n'; lname <- label; char ':'; return lname}

main :: IO ()
main = do
        input <- readFile "enqueue.s"
        print $ (parse test_parser input)
        return ()