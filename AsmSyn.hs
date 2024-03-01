{-# language StandaloneDeriving #-}
{-# language DeriveFunctor #-}
{-# language TypeOperators #-}
{-# language MultiParamTypeClasses #-}
{-# language FlexibleInstances #-}
{-# language FlexibleContexts #-}
{-# LANGUAGE OverlappingInstances #-}

module AsmSyn where

import GHC.Generics
import Control.Monad.Free

import Classes
import Combinator
import Components

-- this is in GHC.Base
-- type String = [Char]

data Para =
    Para_Reg Int                    -- r0
  | Para_Imm Int                    -- #123
  | Para_RegList [Para]             -- {fp, lr}
  | Para_RegBase Para Int Bool      -- [Para, Int]!?

instance Show Para where
  show (Para_Reg x) = 'r':(show x)
  show (Para_Imm x) =  '#':(show x)
  show (Para_RegList xs) = '{':show(xs) ++ "}"
  show (Para_RegBase p offset cb) = if cb then (p_str ++ "]!") else (p_str ++ "]") where
                                        p_str = '[' : show p ++ (',':show offset)


data FuncDecl t = FuncDecl String t
data Comment t = Comment String t
data Push t = Push Para t

deriving instance Functor FuncDecl
deriving instance Functor Comment
deriving instance Functor Push
instance (Show t) => Show (FuncDecl t) where
    show (FuncDecl fname t) = "Show FuncDecl " ++ fname ++ show t
instance (Show t) => Show (Comment t) where
    show (Comment commt t) = "Show Comment -> " ++ commt ++ show t 
instance (Show t) => Show (Push t) where
    show (Push p t) = "Show Push Inst " ++ show p ++ show t

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

func_decl :: (FuncDecl :<: f) => String -> Free f ()
func_decl fname = inject (FuncDecl fname (return ()))

comment :: (Comment :<: f) => String -> Free f ()
comment commt = inject (Comment commt (return ()))

push :: (Push :<: f) => Para -> Free f ()
push p = inject (Push p (return ()))

type CompExpr = FuncDecl :+: Comment :+: Push

input :: String
input = "enqueue:\n\t@ args = 0, pretend = 0, frame = 16\n\t@ frame_needed = 1, uses_anonymous_args = 0\n\tpush\t{fp, lr}\n\tadd\tfp, sp, #4\n\tsub\tsp, sp, #16"

endtoline :: Parser String
endtoline = do { cs <- many $ satp (\ch -> ch /= '\n') item; char '\n'; return cs}

comment_p :: Parser String
comment_p = do { space; symb "@"; endtoline }

func_def :: Parser String
func_def = do
            name <- symb "enqueue"
            symb ":"
            return name

p_reg :: Parser String
p_reg = (do { char 'r'; r1 <- digit; r2 <- digit; return ['r', r1, r2]}) +++ 
        (do { char 'r' ; r1 <- digit; return ['r', r1]}) +++ 
        (symb "fp") +++
        (symb "lr") +++
        (symb "sp") 

p_reglist :: Parser Para
p_reglist = do { char '{'; plist <- sepby p_reg (char ',' ); char '}'; return $ Para_RegList [Para_Reg 1] }

-- expr = funcdel | comment | push
expr :: Parser (Free CompExpr ())
expr = do { name <- func_def; rest $ func_decl name} 
        where
            rest a = do {commt <- comment_p; rest $ do { a; comment commt} } +++
                     do {space; iname <- symb "push"; reg_list <- p_reglist; rest $ do {a; push reg_list}} +++ 
                     return a

res = parse expr input
lres = length res
res1 = fst $ res !! 0
res2 = snd $ res !! 0

a = L1 $ FuncDecl "123" 1 :: CompExpr Int
b = R1 $ L1 $ Comment "456" 2 :: CompExpr Int

c = Pure 1 :: Free CompExpr Int
d = Free (L1 (FuncDecl "1234" (return ())))  :: Free CompExpr ()
e = Free (L1 (FuncDecl "1111" c)) :: Free CompExpr Int
fc = Free (R1 (L1 (Comment "kkkk" e))) :: Free CompExpr Int

ce = do { func_decl "hhhh"; return 1; comment "test"; func_decl "another one"; return () } :: Free CompExpr ()


printCompExpr :: (Show a) => Free CompExpr a -> String
printCompExpr (Pure x) = show x
printCompExpr (Free (L1 (FuncDecl name x))) = "fun_def: " ++ name ++ "\n" ++ printCompExpr x
printCompExpr (Free (R1 (L1 (Comment commt x) ))) = "comment: " ++ commt ++ "\n" ++ printCompExpr x
printCompExpr (Free (R1 (R1 _ ))) = "cao ni ma, this is push\n"

pce = printCompExpr ce
-- expr :: Parser (Free CompExpr ())
-- expr = do { name <- func_def; t <- expr; return $ func_decl name t }

-- expr_comment :: Parser (Free CompExpr ())
-- expr_comment = do {name <- comment_p; return $ comment name }

-- pfunc = parse expr input
-- checkFunc :: Free Expr () -> String
-- checkFunc (Pure s) = show s
-- checkFunc (Free (L1 x)) = show x
-- checkFunc (Free (R1 x)) = show x
{-
data AsmExpr
    = FuncDecl  String
    | Comment   String
    | LabelDecl String
    | Inst1P    Para
    | Inst2P    Para Para
    | Inst3P    Para Para Para
-}