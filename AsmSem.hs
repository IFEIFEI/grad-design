{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# language DeriveFunctor #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}



module AsmSem where

import Control.Lens hiding ((:<))
import Control.Monad.Identity 
import Control.Monad.Free
import Control.Comonad.Cofree
import GHC.Generics
import Data.Map hiding (foldl)

import TypeLogic

import AsmSyn

newtype Register = Register {_word :: Int}
    deriving (Show, Eq)
makeLenses ''Register

byte_reg :: Lens' Register Int
byte_reg = lens getb setb
                    where
                        getb r = mod (r ^. word)  (2^8)
                        setb r x =  r { _word = (div (r ^. word)  (2^8) + x)}

hword_reg :: Lens' Register Int
hword_reg = lens getb setb
                    where
                        getb r = mod (r ^. word)  (2^16)
                        setb r x =  r { _word = (div (r ^. word)  (2^16) + x)}

data CPSR = 
    CPSR
        { _neg_flag     :: Int
        , _zero_flag    :: Int
        , _carry_flag   :: Int
        , _overf_flag   :: Int 
        , _underf_flag  :: Int 
        }
    deriving(Show, Eq)
makeLenses ''CPSR

type Addr = Int
type Value = Int
data Mem =
    Mem {_mmap :: Addr -> Value }

mlook :: Mem -> Addr -> Value
mlook (Mem f) addr = f addr

update_mem :: Mem -> Addr -> Value -> Mem
update_mem mem addr value = Mem $ \x -> if x == addr then value else mlook mem addr 

data Sys_state = 
    Sys_state
      { _reg_list :: [Register]
      , _cpsr     :: CPSR
      , _mem      :: Mem
--      , _symbols  :: Map String Int
      }
makeLenses ''Sys_state 

newtype CoFuncDecl a = CoFuncDecl (String -> a)
newtype CoComment a = CoComment (String -> a)
newtype CoPush a = CoPush (Para -> a)
newtype CoAdd t = CoAdd (Para -> Para -> Para -> t) deriving(Functor)
newtype CoSub t = CoSub (Para -> Para -> Para -> t) deriving(Functor)
newtype CoMul t = CoMul (Para -> Para -> Para -> t) deriving(Functor)
newtype CoLsl t = CoLsl (Para -> Para -> Para -> t) deriving(Functor)
newtype CoLdrb t = CoLdrb (Para -> Para -> t)    deriving(Functor)
newtype CoStr t = CoStr (Para -> Para -> t)      deriving(Functor)
newtype CoLdr t = CoLdr (Para -> Para -> t)      deriving(Functor)
newtype CoCmp t = CoCmp (Para -> Para -> t)      deriving(Functor)
newtype CoBne t = CoBne (Para -> t)           deriving(Functor)
newtype CoBxx t = CoBxx (Para -> t)           deriving(Functor)
newtype CoPop t = CoPop (Para -> t)           deriving(Functor)
newtype CoLabel t = CoLabel (String -> t)     deriving(Functor)
newtype CoNop t = CoNop t                deriving(Functor)
newtype CoAttr_align t = CoAttr_align (Int -> t)  deriving (Functor)
newtype CoAttr_word  t = CoAttr_word  (String -> t) deriving (Functor)


deriving instance Functor CoFuncDecl
deriving instance Functor CoComment
deriving instance Functor CoPush

type CoIntp = CoFuncDecl :*: CoComment :*: CoPush :*: CoAdd :*: CoSub :*: CoMul :*: CoLsl
              :*: CoLdrb :*: CoStr :*: CoLdr :*: CoCmp :*: CoAttr_word
              :*: CoBne :*: CoBxx :*: CoPop :*: CoLabel :*: CoNop :*: CoAttr_align

-- type PlaceType = Sys_state
-- codeline number and generated isabella code
data LabelType = FunctionDecl | LabelDecl
data AsmCodeBlock =
     AsmCodeBlock
     { _label_name :: String
     , _block_type  :: LabelType
     , _start :: Int
     , _end   :: Int
     }
makeLenses ''AsmCodeBlock
data Isa_code = 
     Isa_code
      { _code_num :: Int
      , _block    :: [AsmCodeBlock]
      , _tgt_code :: String
      , _symbols  :: Map String (String, Int)       -- symbol -> (label, offset)
      }
makeLenses ''Isa_code 
-- type PlaceType = (Int, String)
type PlaceType = Isa_code

coFuncDecl :: PlaceType -> String -> PlaceType
coFuncDecl s fname = s & block %~ (\xs -> func_block : xs)
                        where
                            func_block = AsmCodeBlock fname FunctionDecl start_n start_n    -- end number will be modified later
                            start_n = s ^. code_num                 

coComment :: PlaceType -> String -> PlaceType
coComment s cmt = s

coPush :: PlaceType -> Para -> PlaceType
coPush s p = s & code_num %~ (+1) & tgt_code %~ new_s
                where
                    n       = s ^. code_num + 1
                    new_s x = x ++ spec ++ func ++ lemma
                    spec    = single_para_spec n push_op p
                    func    = genFuncName n
                    lemma   = genParaLemma n push_op p

coAdd :: PlaceType -> Para -> Para -> Para -> PlaceType
coAdd s p1 p2 p3 = s & code_num %~ (+1) & tgt_code %~ new_s
                        where
                            n       = s ^. code_num + 1
                            new_s x = x ++ spec ++ func ++ lemma
                            spec    = triple_para_spec n add_op p1 p2 p3
                            func    = genFuncName n
                            lemma   = gen3ParaLemma n add_op p1 p2 p3

coSub :: PlaceType -> Para -> Para -> Para -> PlaceType
coSub s p1 p2 p3 = s & code_num %~ (+1) & tgt_code %~ new_s
                        where
                            n       = s ^. code_num + 1
                            new_s x = x ++ spec ++ func ++ lemma
                            spec    = triple_para_spec n sub_op p1 p2 p3
                            func    = genFuncName n
                            lemma   = gen3ParaLemma n sub_op p1 p2 p3

coMul :: PlaceType -> Para -> Para -> Para -> PlaceType
coMul s p1 p2 p3 = s & code_num %~ (+1) & tgt_code %~ new_s
                        where
                            n       = s ^. code_num + 1
                            new_s x = x ++ spec ++ func ++ lemma
                            spec    = triple_para_spec n mul_op p1 p2 p3
                            func    = genFuncName n
                            lemma   = gen3ParaLemma n mul_op p1 p2 p3

coLsl :: PlaceType -> Para -> Para -> Para -> PlaceType
coLsl s p1 p2 p3 = s & code_num %~ (+1) & tgt_code %~ new_s
                        where
                            n       = s ^. code_num + 1
                            new_s x = x ++ spec ++ func ++ lemma
                            spec    = triple_para_spec n lsl_op p1 p2 p3
                            func    = genFuncName n
                            lemma   = gen3ParaLemma n lsl_op p1 p2 p3

coLdrb :: PlaceType -> Para -> Para -> PlaceType
coLdrb s p1 p2 = s & code_num %~ (+1) & tgt_code %~ new_s
                    where
                        n       = s ^. code_num + 1
                        new_s x = x ++ spec ++ func ++ lemma
                        spec    = double_para_spec n ldrb_op p1 p2
                        func    = genFuncName n
                        lemma   = gen2ParaLemma n ldrb_op p1 p2

coStr :: PlaceType -> Para -> Para -> PlaceType
coStr s p1 p2 = s & code_num %~ (+1) & tgt_code %~ new_s
                    where
                        n       = s ^. code_num + 1
                        new_s x = x ++ spec ++ func ++ lemma
                        spec    = double_para_spec n str_op p1 p2
                        func    = genFuncName n
                        lemma   = gen2ParaLemma n str_op p1 p2

coLdr :: PlaceType -> Para -> Para -> PlaceType
coLdr s p1 p2 = s & code_num %~ (+1) & tgt_code %~ new_s
                    where
                        n       = s ^. code_num + 1
                        new_s x = x ++ spec ++ func ++ lemma
                        spec    = double_para_spec n ldr_op p1 p2
                        func    = genFuncName n
                        lemma   = gen2ParaLemma n ldr_op p1 p2

coCmp :: PlaceType -> Para -> Para -> PlaceType
coCmp s p1 p2 = s & code_num %~ (+1) & tgt_code %~ new_s
                    where
                        n       = s ^. code_num + 1
                        new_s x = x ++ spec ++ func ++ lemma
                        spec    = double_para_spec n cmp_op p1 p2
                        func    = genFuncName n
                        lemma   = gen2ParaLemma n cmp_op p1 p2

coAttr_word :: PlaceType -> String -> PlaceType
coAttr_word s var = s & code_num %~ (+1)
                      & symbols %~ (insert var (lname, offset))
                      where
                        n      = s ^. code_num + 1
                        lname  = (s ^. block) !! 0 ^. label_name
                        offset = (n+1) - (s ^. block) !! 0 ^. start

coBne :: PlaceType -> Para -> PlaceType
coBne s p1  = s & code_num %~ (+1) & tgt_code %~ new_s
                where
                    n       = s ^. code_num + 1
                    new_s x = x ++ spec ++ func ++ lemma
                    spec    = single_para_spec n bne_op p1
                    func    = genFuncName n
                    lemma   = genParaLemma n bne_op p1

coBxx :: PlaceType -> Para -> PlaceType
coBxx s p1  = s & code_num %~ (+1) & tgt_code %~ new_s
                where
                    n       = s ^. code_num + 1
                    new_s x = x ++ spec ++ func ++ lemma
                    spec    = single_para_spec n bxx_op p1
                    func    = genFuncName n
                    lemma   = genParaLemma n bxx_op p1

coPop :: PlaceType -> Para -> PlaceType
coPop s p1  = s & code_num %~ (+1) & tgt_code %~ new_s
                where
                    n       = s ^. code_num + 1
                    new_s x = x ++ spec ++ func ++ lemma
                    spec    = single_para_spec n pop_op p1
                    func    = genFuncName n
                    lemma   = genParaLemma n pop_op p1

coLabel :: PlaceType -> String -> PlaceType
coLabel s lname = s & code_num %~ (+1) 
                    & block . ix 0 . end .~ start_n 
                    & block %~ (\xs -> new_block : xs)
                    where
                        new_block = AsmCodeBlock lname LabelDecl start_n start_n
                        start_n = s ^. code_num 

coNop :: PlaceType -> PlaceType
coNop = id

coAttr_align :: PlaceType -> Int -> PlaceType
coAttr_align = undefined

coMov :: PlaceType -> Para -> Para -> PlaceType
coMov s p1 p2 = s & code_num %~ (+1) & tgt_code %~ new_s
                    where
                        n       = s ^. code_num + 1
                        new_s x = x ++ spec ++ func ++ lemma
                        spec    = double_para_spec n mov_op p1 p2
                        func    = genFuncName n
                        lemma   = gen2ParaLemma n mov_op p1 p2

interpretSystem :: PlaceType -> Cofree CoIntp PlaceType
interpretSystem sys = coiter next start
                    where
                        next s = (CoFuncDecl $ coFuncDecl s) :*: (CoComment $ coComment s) :*: (CoPush $ coPush s) :*:
                                 (CoAdd $ coAdd s) :*: (CoSub $ coSub s) :*: (CoMul $ coMul s) :*:
                                 (CoLsl $ coLsl s) :*: (CoLdrb $ coLdrb s) :*: (CoStr $ coStr s) :*:
                                 (CoLdr $ coLdr s) :*: (CoCmp $ coCmp s) :*: (CoAttr_word $ coAttr_word s) :*:
                                 (CoBne $ coBne s) :*: (CoBxx $ coBxx s) :*: (CoPop $ coPop s) :*:
                                 (CoLabel $ coLabel s) :*: (CoNop $ coNop s) :*: (CoAttr_align $ coAttr_align s)
                        start  = sys

invLProd :: (Functor f, Functor g) => (f :*: g) a -> f a
invLProd (fa :*: _) = fa
invRProd :: (Functor f, Functor g) => (f :*: g) a -> g a
invRProd (_ :*: ga) = ga

instance (Functor f, Functor g) => (f :*: g) :<: f where
    inj = invLProd
instance (Functor f, Functor g, Functor h, g :<: f) => (h :*: g) :<: f  where
    inj = inj . invRProd

-- closed family will conflict here while using type instance to
-- declare each paired types, there should be some way to decopose
-- them, and the default pair should also be considered to try at the last
type family PairPred (f :: * -> *) (g :: * -> *) :: * where
    PairPred Identity Identity = HTrue
    PairPred ((->) a) ((,) a) = HTrue
    PairPred ((,) a) ((->) a) = HTrue
    PairPred f (g :+: k) = And (CastHTrue (PairPred f g)) (CastHTrue (PairPred f k))
    PairPred (f :*: h) k = Or (CastHTrue (PairPred f k))  (CastHTrue (PairPred h k))
    PairPred (Cofree f) (Free g) = HTrue
    -- co pair 
    PairPred CoFuncDecl FuncDecl = HTrue
    PairPred CoComment Comment = HTrue
    PairPred CoPush Push = HTrue
    PairPred CoAdd Add = HTrue 
    PairPred CoSub Sub = HTrue 
    PairPred CoMul Mul = HTrue 
    PairPred CoLsl Lsl = HTrue 
    PairPred CoLdrb Ldrb = HTrue
    PairPred CoStr Str = HTrue 
    PairPred CoLdr Ldr = HTrue 
    PairPred CoCmp Cmp = HTrue 
    PairPred CoAttr_word Attr_word = HTrue
    PairPred CoBne Bne = HTrue 
    PairPred CoBxx Bxx = HTrue 
    PairPred CoPop Pop = HTrue 
    PairPred CoLabel Label = HTrue
    PairPred CoNop Nop = HTrue 
    PairPred CoAttr_align Attr_align = HTrue
    -- defalut pair
    PairPred f g = HFalse

-- type instance PairPred CoFuncDecl FuncDecl = HTrue

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
instance {-# OVERLAPs #-} Pairing' HTrue ((->) a) ((,) a) where
    pair' _ p f = uncurry (p . f)
instance {-# OVERLAPs #-} Pairing' HTrue ((,) a) ((->) a) where
    pair' _ p f g = pair (flip p) g f
instance {-# OVERLAPs #-} Pairing f g => Pairing' HTrue (Cofree f) (Free g) where
    pair' _ p (a :< _ ) (Pure x)  = p a x
    pair' _ p (_ :< fs) (Free gs) = pair (pair p) fs gs
instance {-# OVERLAPs #-} (Pairing g f, Pairing g h) => Pairing' HTrue g (f :+: h) where
    pair' _ p g (L1 f) = pair p g f
    pair' _ p g (R1 h) = pair p g h
instance {-# OVERLAPs #-} (Functor h, Or (CastHTrue (PairPred f g)) (PairPred h g) ~ HLTrue, Pairing f g) => Pairing' HLTrue (f :*: h) g where
    pair' _ p (f :*: h) g = pair p f g
instance {-# OVERLAPs #-} (Functor f, Or (PairPred f g) (CastHTrue (PairPred h g)) ~ HRTrue, Pairing h g) => Pairing' HRTrue (f :*: h) g where
    pair' _ p (f :*: h) g = pair p h g

instance {-# OVERLAPs #-} Pairing' HTrue CoFuncDecl FuncDecl where
    pair' _ f (CoFuncDecl d) (FuncDecl s t) = f (d s) t
instance {-# OVERLAPs #-} Pairing' HTrue CoComment Comment where
    pair' _ f (CoComment c) (Comment s t) =  f (c s) t
instance {-# OVERLAPs #-} Pairing' HTrue CoPush Push where
    pair' _ f (CoPush fp) (Push p t) = f (fp p) t
instance {-# OVERLAPs #-} Pairing' HTrue CoAdd Add  where
    pair' _ f _ _ = undefined  
instance {-# OVERLAPs #-} Pairing' HTrue CoSub Sub  where
    pair' _ f _ _ = undefined  
instance {-# OVERLAPs #-} Pairing' HTrue CoMul Mul  where
    pair' _ f _ _ = undefined  
instance {-# OVERLAPs #-} Pairing' HTrue CoLsl Lsl  where
    pair' _ f _ _ = undefined  
instance {-# OVERLAPs #-} Pairing' HTrue CoLdrb Ldrb  where
    pair' _ f _ _ = undefined 
instance {-# OVERLAPs #-} Pairing' HTrue CoStr Str  where
    pair' _ f _ _ = undefined  
instance {-# OVERLAPs #-} Pairing' HTrue CoLdr Ldr  where
    pair' _ f _ _ = undefined  
instance {-# OVERLAPs #-} Pairing' HTrue CoCmp Cmp  where
    pair' _ f _ _ = undefined  
instance {-# OVERLAPs #-} Pairing' HTrue CoAttr_word Attr_word  where
    pair' _ f _ _ = undefined 
instance {-# OVERLAPs #-} Pairing' HTrue CoBne Bne  where
    pair' _ f _ _ = undefined  
instance {-# OVERLAPs #-} Pairing' HTrue CoBxx Bxx  where
    pair' _ f _ _ = undefined  
instance {-# OVERLAPs #-} Pairing' HTrue CoPop Pop  where
    pair' _ f _ _ = undefined  
instance {-# OVERLAPs #-} Pairing' HTrue CoLabel Label  where
    pair' _ f _ _ = undefined 
instance {-# OVERLAPs #-} Pairing' HTrue CoNop Nop  where
    pair' _ f _ _ = undefined  
instance {-# OVERLAPs #-} Pairing' HTrue CoAttr_align Attr_align  where
    pair' _ f _ _ = undefined 

-- s :: Sys_state
-- s = Sys_state [] (CPSR 0 0 0 0 0) (Mem undefined) empty
-- syn_expr = do { func_decl "test func"; comment "comment here"} :: Free CompExpr ()

-- synt = pair (flip const) (interpretSystem s) syn_expr
-- semt = pair const (interpretSystem s) syn_expr

{- example output code
(****************************************************************
          1  0x9b0_0x9b0:  push               EBP
****************************************************************)

definition g9b0_9b0 ::  "state \<Rightarrow> state" where  [my_def]:
"g9b0_9b0 s  = s\<lparr>
    sKM:=(sKM s) (
        ESP0 -4 :=EBP(sR s)
    ),
    sR:=sR s\<lparr>
      ESP :=ESP(sR s) - 0x4,
      EIP :=0x9b1
    \<rparr>
  \<rparr>"


definition F9b0_9b0 :: "state \<Rightarrow> state" where  [my_def]:
"F9b0_9b0 s = g9b0_9b0 s"

lemma L9b0_9b0:
  assumes  " prec s = True "
  shows      "F9b0_9b0  s = s\<lparr>
    sKM:=(sKM s) (
        ESP0 -4 := EBP(sR s)
    ),
    sR := sR s \<lparr>
        ESP := 0xfffffc,
        EIP := 0x9b1 
    \<rparr> 
  \<rparr> "
  using assms  by (auto simp : my_def fun_upd_twist )

-}

def_fname = "definition "
def_type = "::  \"state \\<Rightarrow> state\" where  [my_def]:\n"

-- state = (reg_list, stack , mem)
wrap_sp str = "(" ++ str ++ ")" 
def_reg_get x = " ^. reglist . " ++ x 
def_reg_get_s s x = s ++ def_reg_get x 
def_reg_set x b = " & reglist . " ++ x ++ " .~ " ++ b
def_reg_set_s s x b = s ++ def_reg_set x b
def_reg_over x f = " & reglist . " ++ x ++ " %~ " ++ (wrap_sp f)
def_reg_over_s s x f = s ++ def_reg_over x (wrap_sp f)
def_mem_get x = " ^. mem " ++ x
def_mem_get_s s x = s ++ def_mem_get x
def_mem_set x v = def_mem_over "update " ++ x ++ " " ++ v
def_mem_set_s s x v = s ++ def_mem_set x v
def_mem_over f = " & mem %~ " ++ (wrap_sp f)
def_mem_over_s s f = s ++ def_mem_over f   

-- only operate on one byte
def_reg_getb x = " ^. reglist . " ++ x ++ " . byte" 
def_reg_getb_s s x = s ++ def_reg_get x 
def_reg_setb x b = " & reglist . " ++ x ++ " . byte .~ " ++ b
def_reg_setb_s s x b = s ++ def_reg_set x b
def_reg_overb x f = " & reglist . " ++ x ++ " . byte %~ " ++ f
def_reg_overb_s s x f = s ++ def_reg_over x f
def_mem_getb x = " ^. mem . byte " ++ x
def_mem_getb_s s x = s ++ def_mem_get x
def_mem_setb x v = def_mem_overb "update " ++ x ++ " " ++ v
def_mem_setb_s s x v = s ++ def_mem_set x v
def_mem_overb f = " & mem . byte %~ " ++ (wrap_sp f)
def_mem_overb_s s f = s ++ def_mem_over f 

def_para_get :: String -> Para -> String
def_para_get s (Para_Reg x) = def_reg_get_s "s" (show x)
def_para_get s (Para_Imm imm) = show imm
def_para_get s (Para_RegBase p1 p2) = wrap_sp $ (def_para_get s p1 ++ " + " ++ def_para_get s p2)
def_para_get s (Para_Mem p) = wrap_sp $ (def_para_get s p)
def_para_get s _ = error "Parameter conversion not allowed"

lemma_assum = "assumes  \" prec s = True \" \n"
proof = "using assms  by (auto simp : my_def fun_upd_twist )"

push_op :: Para -> String
push_op  (Para_RegList xs) = new_s 
                where
                    new_s = def_reg_over_s (foldl pr "s" xs) "r15" "+1"
                    pr s x = s ++ (def_reg_over "r13" "-4") ++ (def_reg_set "r13" (show x))
push_op  _ =  error "Invalid parameter for push insturction"

push_spec :: Int -> Para -> String
push_spec n pl = 
        def_fname ++ fname ++ def_type
        ++ fname ++ " s = " ++ new_s ++ "\"\n" 
            where 
                fname = "\" g"++ show n ++ "_" ++ show (n+1)
                new_s = push_op pl

genFuncName :: Int -> String
genFuncName n = def_fname ++ fname ++ def_type
               ++ fname ++ " s = " ++ result ++ " s\"\n"
                 where
                    fname = "\"F" ++ show n ++ "_" ++ show (n + 1)
                    result = "g"++ show n ++ "_" ++ show (n+1)

genPushLemma :: Int -> Para -> String
genPushLemma n pl = "lemma " ++ lname  ++ lemma_assum ++ show_content ++ proof
                where
                    lname = "L" ++ show n ++ "_" ++ show (n+1) ++ "\n:"
                    show_content =  "shows \" F" ++ show n ++ show (n+1) ++ " s = " ++ (push_op pl) ++ "\"\n"

pop_op :: Para -> String
pop_op  (Para_RegList xs) = new_s 
                where
                    new_s = def_reg_over_s (foldl pr "s" xs) "r15" "+1"
                    pr s x = s ++ (def_reg_set (show x) (def_reg_get_s "s" "r13")) ++ (def_reg_over "r13" "+4")
pop_op  _ =  error "Invalid parameter for push insturction"

pop_spec :: Int -> Para -> String
pop_spec n pl = 
        def_fname ++ fname ++ def_type
        ++ fname ++ " s = " ++ new_s ++ "\"\n" 
            where 
                fname = "\" g"++ show n ++ "_" ++ show (n+1)
                new_s = pop_op pl

add_op :: Para -> Para -> Para -> String
add_op r1 r2 r3 = new_s
            where 
                new_s = def_reg_set_s "s" (show r1) addv
                addv = wrap_sp $ v1 ++ " + " ++ v2
                v1 = def_para_get "s" r2
                v2 = def_para_get "s" r3

sub_op :: Para -> Para -> Para -> String
sub_op r1 r2 r3 = new_s
            where 
                new_s = def_reg_set_s "s" (show r1) addv
                addv = wrap_sp $ v1 ++ " - " ++ v2
                v1 = def_para_get "s" r2
                v2 = def_para_get "s" r3

mul_op :: Para -> Para -> Para -> String
mul_op r1 r2 r3 = new_s
            where 
                new_s = def_reg_set_s "s" (show r1) addv
                addv = wrap_sp $ v1 ++ " * " ++ v2
                v1 = def_para_get "s" r2
                v2 = def_para_get "s" r3

lsl_op :: Para -> Para -> Para -> String
lsl_op r1 r2 r3 = new_s
            where
                new_s = def_reg_set_s "s" (show r1) lslv
                lslv = wrap_sp $ "logicShiftLeft " ++ (def_reg_get_s "s" (show r2)) ++ " " ++ (wrap_sp (def_para_get "s" r3)) 

ldrb_op :: Para -> Para -> String
ldrb_op r1 r2 = new_s
                    where
                        new_s = def_reg_setb_s "s" (show r1) (wrap_sp mem_v)
                        mem_v = def_mem_getb_s "s" (wrap_sp addr)
                        addr  = def_para_get "s" r2  

str_op :: Para -> Para -> String
str_op r1 r2 =  new_s
                    where
                        new_s = def_mem_set_s "s" (wrap_sp mem_addr) (def_reg_get_s "s" (show r1))
                        mem_addr = def_para_get "s" r2

ldr_op :: Para -> Para -> String
ldr_op r1 r2 =  new_s
                    where
                        new_s = def_reg_set_s "s" (show r1) (wrap_sp mem_v)
                        mem_v = def_mem_get_s "s" (wrap_sp addr)
                        addr  = def_para_get "s" r2  

cmp_op :: Para -> Para -> String
cmp_op r1 r2 =  new_s
                    where
                        new_s = def_reg_set_s "s" "cspr" (cmp_result)
                        cmp_result = wrap_sp $ "cmpCmp " ++ (def_para_get "s" r1) ++ (def_para_get "s" r2)        

bne_op :: Para -> String
bne_op r1 = new_s
                where
                    new_s = "CheckFlagZero " ++ wrap_sp (def_reg_get_s "s" "cspr . zero_flag") ++ " " ++ wrap_sp (def_para_get "s" r1) 

bxx_op :: Para -> String
bxx_op r1 = new_s
                where
                    new_s = "Check " ++ (def_para_get "s" r1)

mov_op :: Para -> Para -> String
mov_op r1 r2 = new_s
                where 
                    new_s = def_reg_set_s "s" (show r1) (def_para_get "s" r2)

single_para_spec :: Int -> (Para -> String) -> Para -> String
single_para_spec n op_1 p1 = 
            def_fname ++ fname ++ def_type
            ++ fname ++ " s = " ++ new_s ++ "\"\n" 
            where 
                fname = "\" g"++ show n ++ "_" ++ show (n+1)
                new_s = op_1 p1

double_para_spec :: Int -> (Para -> Para -> String) -> Para -> Para -> String
double_para_spec n op_2 p1 p2 = 
            def_fname ++ fname ++ def_type
            ++ fname ++ " s = " ++ new_s ++ "\"\n" 
            where 
                fname = "\" g"++ show n ++ "_" ++ show (n+1)
                new_s = op_2 p1 p2

triple_para_spec :: Int -> (Para -> Para -> Para -> String) -> Para -> Para -> Para -> String
triple_para_spec n op_3 p1 p2 p3 = 
            def_fname ++ fname ++ def_type
            ++ fname ++ " s = " ++ new_s ++ "\"\n" 
            where 
                fname = "\" g"++ show n ++ "_" ++ show (n+1)
                new_s = op_3 p1 p2 p3

genParaLemma :: Int -> (Para -> String) -> Para -> String
genParaLemma n op_1 p1 = "lemma " ++ lname  ++ lemma_assum ++ show_content ++ proof
                where
                    lname = "L" ++ show n ++ "_" ++ show (n+1) ++ "\n:"
                    show_content =  "shows \" F" ++ show n ++ show (n+1) ++ " s = " ++ (op_1 p1) ++ "\"\n"

gen2ParaLemma :: Int -> (Para -> Para -> String) -> Para -> Para -> String
gen2ParaLemma n op_2 p1 p2 = "lemma " ++ lname  ++ lemma_assum ++ show_content ++ proof
                where
                    lname = "L" ++ show n ++ "_" ++ show (n+1) ++ "\n:"
                    show_content =  "shows \" F" ++ show n ++ show (n+1) ++ " s = " ++ (op_2 p1 p2) ++ "\"\n"

gen3ParaLemma :: Int -> (Para -> Para -> Para -> String) -> Para -> Para -> Para -> String
gen3ParaLemma n op_3 p1 p2 p3 = "lemma " ++ lname  ++ lemma_assum ++ show_content ++ proof
                where
                    lname = "L" ++ show n ++ "_" ++ show (n+1) ++ "\n:"
                    show_content =  "shows \" F" ++ show n ++ show (n+1) ++ " s = " ++ (op_3 p1 p2 p3) ++ "\"\n"


