module Components where

import Data.Char

import Classes
import Combinator

{- parse a simple character -}
char :: Char -> Parser Char
char c = sat (c == )

string :: String -> Parser String
string "" = return ""
string (c:cs) = do {char c; string cs; return (c:cs)}

string_any :: Parser String
string_any = do
            ch <- item
            cs <- string_any
            return (ch:cs)

space :: Parser String
space = many $ sat isSpace

digit :: Parser Char
digit = sat $ isDigit

lower :: Parser Char
lower = sat $ isLower

upper :: Parser Char
upper = sat $ isUpper

token :: Parser a -> Parser a
token p = do {a <- p; space; return a}

symb :: String -> Parser String
symb cs = token $ string cs

apply :: Parser a -> String -> [(a,String)]
apply p = parse $ do {space; p}
