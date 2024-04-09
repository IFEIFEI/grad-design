{-# language StandaloneDeriving #-}
{-# language DeriveFunctor #-}
{-# language TypeOperators #-}
{-# language MultiParamTypeClasses #-}
{-# language FlexibleInstances #-}
{-# language FlexibleContexts #-}
{-# LANGUAGE OverlappingInstances #-}


module AsmSyn where

import GHC.Generics
import Data.Char
import Control.Monad.Free

import Classes
import Combinator
import Components

-- this is in GHC.Base
-- type String = [Char]

-- an instruction parameter could be 
-- para = register | imm | reg list
--        [reg]    | [reg, imm] | label arith expression
data Para =
    Para_Reg Int                    -- r0
  | Para_Imm Int                    -- #123
  | Para_RegList [Para]             -- {fp, lr}
  | Para_RegBase Para Para          -- [Para, Int]
  | Para_Mem Para                   -- [Para]
  | Para_Label String Int           -- .Lablel+x
  | Para_Func String                -- single

-- sb 9, sl 10, fp 11, ip 12, sp 13, lr 14, pc 15
p_reg :: Parser Para
p_reg = (do { char 'r'; r1 <- digit; r2 <- digit; return $ Para_Reg (read [r1,r2])}) +++ 
        (do { char 'r' ; r1 <- digit; return $ Para_Reg (digitToInt r1)}) +++ 
        (do { symb "fp"; return $ Para_Reg 11}) +++
        (do { symb "lr"; return $ Para_Reg 14}) +++
        (do { symb "pc"; return $ Para_Reg 15}) +++
        (do { symb "sp"; return $ Para_Reg 13}) 

p_reglist :: Parser Para
p_reglist = do { char '{'; plist <- sepby p_reg (char ',' ); char '}'; return $ Para_RegList plist}

p_imm :: Parser Para
p_imm = do {symb "#-"; imm <- many digit; return $ Para_Imm (read ('-':imm)) } +++
        do {char '#';  imm <- many digit; return $ Para_Imm (read imm)}

p_ri = p_reg +++ p_imm 

p_regbase :: Parser Para
p_regbase = do { char '[';  reg <- p_reg; char ','; space; 
                 imm <- p_imm; char ']';  return $ Para_RegBase reg imm}

-- [r1]
p_mem :: Parser Para
p_mem = do { char '[';  reg <- p_reg; char ']';  return $ Para_Mem reg }

p_label :: Parser Para
p_label = do { symb ".L"; label <- many digit; char '+'; imm <- many digit; return $ Para_Label label (read imm)} +++
          do { symb ".L"; label <- many digit; char '-'; imm <- many digit; return $ Para_Label label (read ('-':imm))} +++
          do { symb ".L"; label <- many digit; return $ Para_Label label 0}

p_func :: Parser Para
p_func = do { name <- endtoline; return $ Para_Func name }

p_para = p_ri +++ p_reglist +++ p_regbase +++ p_mem +++ p_label +++ p_func
all_para = sepby p_para (char ',' )

data FuncDecl t = FuncDecl String t
data Comment t = Comment String t
-- iname_list :: [String]
-- iname_list = ["push", "add", "sub", "mov", "ldrb", "str", 
--               "ldr", "mul", "lsl", "cmp", "bne",
--               "b", "pop"]
data Push t = Push Para t
data Add t = Add Para Para Para t 
data Sub t = Sub Para Para Para t
data Mul t = Mul Para Para Para t deriving(Functor, Show)
data Lsl t = Lsl Para Para Para t deriving(Functor, Show)
data Ldrb t = Ldrb Para Para t    deriving(Functor, Show)
data Str t = Str Para Para t      deriving(Functor, Show)
data Ldr t = Ldr Para Para t      deriving(Functor, Show)
data Cmp t = Cmp Para Para t      deriving(Functor, Show)
data Bne t = Bne Para t           deriving(Functor, Show)
data Bxx t = Bxx Para t           deriving(Functor, Show)
data Pop t = Pop Para t           deriving(Functor, Show)
data Label t = Label String t     deriving(Functor, Show)
data Nop t = Nop t                deriving(Functor, Show)
data Attr_align t = Attr_align Int    t deriving (Functor, Show)
data Attr_word  t = Attr_word  String t deriving (Functor, Show)

deriving instance Functor FuncDecl
deriving instance Functor Comment
deriving instance Functor Push
deriving instance Functor Add
deriving instance Functor Sub

instance (Show t) => Show (FuncDecl t) where
    show (FuncDecl fname t) = "Show FuncDecl " ++ fname ++ show t
instance (Show t) => Show (Comment t) where
    show (Comment commt t) = "Show Comment -> " ++ commt ++ show t 
instance (Show t) => Show (Push t) where
    show (Push p t) = "Show Push Inst " ++ show p ++ show t
instance (Show t) => Show (Add t) where
    show (Add p1 p2 p3 t) = "Show Add Inst " ++ show p1 ++ show p2 ++ show p3 ++ show t
instance (Show t) => Show (Sub t) where
    show (Sub p1 p2 p3 t) = "Show Sub Inst " ++ show p1 ++ show p2 ++ show p3 ++ show t

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

liftinj :: (g :<: f) => Free g a -> Free f a
liftinj (Pure a) = return a
liftinj (Free ga) = inject (fmap liftinj ga) 

func_decl :: (FuncDecl :<: f) => String -> Free f ()
func_decl fname = inject (FuncDecl fname (return ()))

comment :: (Comment :<: f) => String -> Free f ()
comment commt = inject (Comment commt (return ()))

push :: (Push :<: f) => Para -> Free f ()
push p = inject (Push p (return ()))

add :: (Add :<: f) => Para -> Para -> Para -> Free f ()
add p1 p2 p3 = inject (Add p1 p2 p3 (return ()))

sub :: (Sub :<: f) => Para -> Para -> Para -> Free f ()
sub p1 p2 p3 = inject (Sub p1 p2 p3 (return ()))

mul :: (Mul :<: f) => Para -> Para -> Para -> Free f ()
mul p1 p2 p3 = inject (Mul p1 p2 p3 (return ()))

lsl :: (Lsl :<: f) => Para -> Para -> Para -> Free f ()
lsl p1 p2 p3 = inject (Lsl p1 p2 p3 (return ()))

ldrb :: (Ldrb :<: f) => Para -> Para -> Free f ()
ldrb p1 p2 = inject (Ldrb p1 p2(return ()))

str :: (Str :<: f) => Para -> Para -> Free f ()
str p1 p2 = inject (Str p1 p2 (return ()))

ldr :: (Ldr :<: f) => Para -> Para -> Free f ()
ldr p1 p2 = inject (Ldr p1 p2 (return ()))

cmp :: (Cmp :<: f) => Para -> Para -> Free f ()
cmp p1 p2 = inject (Cmp p1 p2 (return ()))

bne :: (Bne :<: f) => Para -> Free f ()
bne p = inject (Bne p (return ()))

bxx :: (Bxx :<: f) => Para -> Free f ()
bxx p = inject (Bxx p (return ()))

pop :: (Pop :<: f) => Para -> Free f ()
pop p = inject (Pop p (return ()))

label :: (Label :<: f) => String -> Free f ()
label s = inject (Label s (return ()))

nop :: (Nop :<: f) => Free f ()
nop = inject (Nop (return ()))

attr_align :: (Attr_align :<: f) => Int -> Free f ()
attr_align x = inject (Attr_align x (return ()))

attr_word :: (Attr_word :<: f) => String -> Free f ()
attr_word x = inject (Attr_word x (return ()))

type CompExpr = FuncDecl :+: Comment :+: Push :+: Add :+: Sub
                :+: Mul :+: Lsl :+: Ldrb :+: Str :+: Ldr :+: Cmp :+: Attr_word
                :+: Bne :+: Bxx :+: Pop :+: Label :+: Nop :+: Attr_align

endtoline :: Parser String
endtoline = do { cs <- many $ satp (\ch -> ch /= '\n') item; char '\n'; return cs}

comment_p :: Parser String
comment_p = do { space; symb "@"; endtoline }

func_def :: Parser String
func_def = do
            name <- symb "enqueue"
            symb ":"
            return name
            
-- expr = funcdel | comment | push
expr :: Parser (Free CompExpr ())
expr = do { name <- func_def; rest $ func_decl name }
        where
            rest a = do {commt <- comment_p; rest $ do { a; comment commt} } +++
                     do {space; iname <- symb "push"; reg_list <- p_reglist; rest $ do {a; push reg_list}} +++ 
                     return a

expr_func :: Parser (Free CompExpr ())
expr_func = do { name <- func_def; return $ func_decl name}

expr_comment :: Parser (Free CompExpr ())
expr_comment = do {commt <- comment_p; return $ comment commt}

lift2P :: (a -> a -> c) -> [a] -> c
lift2P f xs
    | length xs <= 2 = error "lift3p with fewer parater than 3"
    | otherwise = f (xs!!0) (xs !! 1)

lift3P :: (a -> a -> a -> c) -> [a] -> c
lift3P f xs
    | length xs <= 3 = error "lift3p with fewer parater than 3"
    | otherwise = f (xs!!0) (xs !! 1) (xs !! 2)

-- this can be done by fold the list
-- inst_list :: Parser String
-- inst_list = p +++ lp +++ world
--                 where 
--                     p = foldr (+++) (symb "nop") p_list
--                     p_list = map (\s -> symb s) iname_list
--                     lp = do { lname <- label; char ':'; return lname}
--                     world = do {space; symb ".word"; endtoline }
-- push 
expr_push :: Parser (Free CompExpr ())
expr_push = do {space; iname <- symb "push"; reg_list <- p_reglist; return $ push reg_list}

expr_add :: Parser (Free CompExpr ())
expr_add = do {space; iname <- symb "add"; plist <- all_para; return $ lift3P add plist}

expr_sub :: Parser (Free CompExpr ())
expr_sub = do {space; iname <- symb "sub"; plist <- all_para; return $ lift3P sub plist}

expr_mul :: Parser (Free CompExpr ())
expr_mul = do {space; iname <- symb "mul"; plist <- all_para; return $ lift3P mul plist}

expr_lsl :: Parser (Free CompExpr ())
expr_lsl = do {space; iname <- symb "lsl"; plist <- all_para; return $ lift3P lsl plist}

expr_ldrb :: Parser (Free CompExpr ())
expr_ldrb = do {space; iname <- symb "ldrb"; plist <- all_para; return $ lift2P ldrb plist}

expr_str :: Parser (Free CompExpr ())
expr_str = do {space; iname <- symb "str"; plist <- all_para; return $ lift2P str plist}

expr_ldr :: Parser (Free CompExpr ())
expr_ldr = do {space; iname <- symb "ldr"; plist <- all_para; return $ lift2P ldr plist}

expr_cmp :: Parser (Free CompExpr ())
expr_cmp = do {space; iname <- symb "cmp"; plist <- all_para; return $ lift2P cmp plist}

expr_bne :: Parser (Free CompExpr ())
expr_bne = do {space; iname <- symb "bne"; p <- p_para; return $ bne p }

expr_bxx :: Parser (Free CompExpr ())
expr_bxx = do {space; iname <- symb "b"; p <- p_para; return $ bxx p }

expr_pop :: Parser (Free CompExpr ())
expr_pop = do {space; iname <- symb "pop"; reg_list <- p_reglist; return $ pop reg_list}

expr_label :: Parser (Free CompExpr ())
expr_label = do {space; symb ".L"; label_num <- many digit; char ':'; return $ label label_num}

expr_nop :: Parser (Free CompExpr ())
expr_nop = do {space; symb "nop"; return $ nop }

expr_attr_align :: Parser (Free CompExpr ())
expr_attr_align = do {space; symb ".align"; num <- digit; return $ attr_align (digitToInt num)}

expr_attr_word :: Parser (Free CompExpr ())
expr_attr_word = do {space; symb ".word"; name <- endtoline; return $ attr_word name}

-- it can be gathered together by a simple inject method
expr_comp :: Parser (Free CompExpr ())
expr_comp = expr_func +++ expr_comment +++ expr_push +++ expr_add +++ expr_sub
            +++ expr_str +++ expr_ldrb +++ expr_lsl +++ expr_mul
            +++ expr_ldr +++ expr_cmp +++ expr_bne +++ expr_pop +++ expr_bxx 
            +++ expr_label +++ expr_attr_word +++ expr_pop +++ expr_nop +++ expr_attr_align

comp_many :: (Functor f) => Parser (Free f ()) -> Parser (Free f ())  
comp_many p = comp_many1 p +++ (return (return ()))  

comp_many1 ::(Functor f) => Parser (Free f ()) -> Parser (Free f ())  
comp_many1 p = do { a <- p; as <- comp_many p; return $ do {a; as} }

-- compose mov inst
data Mov t = Mov Para Para t
deriving instance Functor Mov
instance (Show t) => Show (Mov t) where
    show (Mov p1 p2 t) = "Show Move Inst " ++ show p1 ++ show p2 ++ show t
mov :: (Mov :<: f) => Para -> Para -> Free f () 
mov p1 p2 = inject $ Mov p1 p2 (return ())

type MovCompExpr = CompExpr :+: Mov
expr_mov :: Parser (Free MovCompExpr ())
expr_mov = do {space; iname <- symb "mov"; plist <- all_para; return $ lift2P mov plist}

expr_new_comp :: (CompExpr :<: MovCompExpr) => Parser (Free CompExpr ()) -> Parser (Free MovCompExpr ())
expr_new_comp p = do { a <- p; return $ liftinj a} +++ expr_mov

-- comp_res = parse expr_comp input
-- comp_res = parse (comp_many expr_comp) input
comp_res = parse (comp_many $ expr_new_comp expr_comp) input
comp_lres = length comp_res
comp_res1 = fst $ comp_res !! 0
comp_res2 = snd $ comp_res !! 0
-- pcomp_res1 = printCompExpr comp_res1

main :: IO ()
main = do
        input <- readFile "enqueue.s"
        print $ snd $ (parse (comp_many $ expr_new_comp expr_comp) input) !! 0
        return ()

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

-- printMovCompExpr :: (Show a) => Free MovCompExpr a -> String
-- printMovCompExpr (Pure x) = show x
-- printMovCompExpr (Free (L1 (FuncDecl name x))) = "fun_def: " ++ name ++ "\n" ++ printCompExpr x
-- printMovCompExpr (Free (R1 (L1 (Comment commt x) ))) = "comment: " ++ commt ++ "\n" ++ printCompExpr x
-- printMovCompExpr (Free (R1 (R1 (L1 _ )))) = "cao ni ma, this is push\n"
-- printMovCompExpr (Free (R1 (R1 (R1 _)))) = "i want to die , this is move instruction\n"

pce = printCompExpr ce
all_para_test = sepby p_para (char ',' )
inst_test = do {symb "push"; space; plist <- all_para_test; return $ "push" ++ show plist }
all_inst_line_test = many (inst_test <&> symb "\n")
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

instance Show Para where
  show (Para_Reg x) = 'r':(show x)
  show (Para_Imm x) =  '#':(show x)
  show (Para_RegList xs) = '{':show(xs) ++ "}"
  show (Para_RegBase p offset) = '[' : show p ++ (',':show offset) ++ "]"
  show (Para_Mem p) = '[' : show p  ++ "]"
  show (Para_Label label offset) = ".L" ++ label ++ " " ++ (show offset)
  show (Para_Func s) = s

input :: String
input = "enqueue:\n\t@ args = 0, pretend = 0, frame = 16\n\t@ frame_needed = 1, uses_anonymous_args = 0\n\tpush\t{fp, lr}\n\tadd\tfp, sp, #4\n\tsub\tsp, sp, #16\n\tmov\tr3, r0"
