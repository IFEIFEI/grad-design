module AsmSem where

{-# LANGUAGE TemplateHaskell #-}

import Control.Lens

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
    Mem {_mem :: Addr -> Value }

mlook :: Mem -> Addr -> Value
mlook (Mem f) addr = f addr

update_mem :: Mem -> Addr -> Value -> Mem
update_mem mem addr value = Mem $ \x -> if x == addr then value else mlook mem addr 

type Sys_state = ([Register], CPSR, Mem) 

