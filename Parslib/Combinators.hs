{-# LANGUAGE FlexibleContexts    
           , MultiParamTypeClasses
           , TypeSynonymInstances
           , FlexibleInstances
#-}

-- TypeSynonymInstances & FlexibleInstances for CombinableParser using Parser as type synonym of Pm

module Parslib.Combinators where 

import Parslib.Parsers
import Control.Applicative hiding ((<**>), many)

-- %%%%% PARSER COMBINATORS %%%%% --   

infixl  3  `opt` 
infixr  4  <:*>
infixl  4  <*:>, <**>, <+*>, <??>
infixl  5  <++>, <?|> 

class (Applicative (p st), Functor (p st), Alternative (p st)) => CombinableParser p st where

instance CombinableParser Parser st

(<**>) :: CombinableParser p st => p st a -> p st (a -> b) -> p st b
p1 <**> p2 = (\a f -> f a) <$> p1 <*> p2

(<:*>) :: CombinableParser p st => p st a -> p st [a] -> p st [a]
p <:*> ps = (:) <$> p <*> ps

(<*:>) :: CombinableParser p st => p st [a] -> p st a -> p st [a]
ps <*:> p = (\a b -> a ++ [b]) <$> ps <*> p

(<+*>) :: CombinableParser p st => p st [a] -> p st [a] -> p st [a]
p <+*> ps = (++) <$> p <*> ps

(<??>) :: CombinableParser p st => p st a -> p st (a -> a) -> p st a
p1 <??> p2 = p1 <**> (p2 `opt` id)

(<++>) :: CombinableParser p st => p st [a] -> p st [a] -> p st [a]
p <++> q = (++) <$> p <*> q

(<?|>) :: CombinableParser p st => p st a -> (b, a -> b) -> p st b
p <?|> (z, f) = (f <$> p) <|> pure z

(?*>) :: CombinableParser p st => p st a ->  p st b -> p st b
p ?*> q = p <?|> (const undefined, undefined) *> q

(<*?) :: CombinableParser p st => p st a -> p st b -> p st a
p <*? q = p <* q <?|> (const undefined, undefined)

opt :: CombinableParser p st => p st a -> a -> p st a
p `opt` v = p <|> pure v

many :: CombinableParser p st => p st a -> p st [a]
many p = p <:*> many p `opt` []

choice :: CombinableParser p st => [p st a] -> p st a
choice ps = foldr (<|>) (empty) ps

many1 :: CombinableParser p st => p st a -> p st [a]
many1 p = p <:*> many p

chainl :: CombinableParser p st => p st (a -> a -> a) -> p st a -> p st a
chainl op p = applyAll <$> p <*> many (flip <$> op <*> p) 

chainr :: CombinableParser p st => p st (a -> a -> a) -> p st a -> p st a
chainr op p = r where r = p <??> (flip <$> op <*> r)

seqnc :: CombinableParser p st => [p st a] -> p st [a]
seqnc (p:ps) = p <:*> seqnc ps
seqnc [] = pure []

applyAll :: a -> [a -> a] -> a
applyAll x (yf:yfs) = applyAll (yf x) yfs
applyAll x [] = x

-- Basic parsers --

pure_token :: (Show b, Describes b a, Provides st b a pos0) => [b] -> Parser st [a]
pure_token (x:xs) = sym x <:*> pure_token xs
pure_token [] = return []

token :: (Describes Char a, Provides st Char a pos) => String -> Parser st [a]
token (xs) = pure_token xs <* spaces

--     -- Iteration --

    -- Packing --

packstr :: (Provides st Char Char pos) => String -> Parser st a -> String -> Parser st a
packstr open p close = pack' (token open) p (token close)

pack :: (Show b, Describes b a', Provides st b a' pos) => [b] -> Parser st a -> [b] -> Parser st a
pack open p close = pack' (pure_token open) p (pure_token close)

pack' :: Parser st b -> Parser st a -> Parser st b -> Parser st a
pack' open p close = open *> p <* close

parens :: (Provides st Char Char pos) => Parser st a -> Parser st a
parens p = packstr "(" p ")"

brackets :: (Provides st Char Char pos) => Parser st a -> Parser st a
brackets p = packstr "[" p "]"

curly :: (Provides st Char Char pos) => Parser st a -> Parser st a
curly p = packstr "{" p "}"

tagged :: (Provides st Char Char pos) => Parser st a -> Parser st a
tagged p = packstr "<" p ">"

singleQuoted :: (Provides st Char Char pos) => Parser st a -> Parser st a
singleQuoted p = packstr "'" p "'"

doubleQuoted :: (Provides st Char Char pos) => Parser st a -> Parser st a
doubleQuoted p = packstr "\"" p "\""

-- String Parsers --

spaces :: (Describes Char a, Provides st Char a pos) => Parser st [a]
spaces = many (choice (map sym [' ', '\t', '\n']))

symSpaces :: (Describes Char a, Provides st Char a pos) => Char -> Parser st a
symSpaces a = sym a <* spaces

letter :: (Provides st Char Char pos) => Parser st Char
letter = choice (map symSpaces "abcdefghijklmnopqrstuvwxyz")

word :: (Provides st Char Char pos) => Parser st String
word = many1 letter

-- String Operators -- 

strUniOp :: (Describes Char a', Provides st Char a' pos) => (a -> b, [Char]) -> Parser st (a -> b)
strUniOp (semantic, s) = uniOp' semantic (token s)

strAnyUniOp :: (Describes Char a', Provides st Char a' pos) => [(a -> b, [Char])] -> Parser st (a -> b)
strAnyUniOp = choice . (map strUniOp)

strBiOp :: (Describes Char a', Provides st Char a' pos) => (a -> b -> c, [Char]) -> Parser st (a -> b -> c)
strBiOp (semantic, s) = biOp' semantic (token s)

strAnyBiOp :: (Describes Char a', Provides st Char a' pos) => [(a -> b -> c, [Char])] -> Parser st (a -> b -> c)
strAnyBiOp = choice . (map strBiOp)

-- Operators --

uniOp :: (Show s, Describes s a', Provides st s a' pos) => (a -> b, [s]) -> Parser st (a -> b)
uniOp (semantic, s) = uniOp' semantic (pure_token s)

uniOp' :: (a -> b) -> Parser st c -> Parser st (a -> b)
uniOp' semantic uniOp_reader = semantic <$ uniOp_reader

anyUniOp :: (Show s, Describes s a', Provides st s a' pos) => [(a -> b, [s])] -> Parser st (a -> b)
anyUniOp = choice . (map uniOp)

biOp :: (Show s, Describes s a', Provides st s a' pos) => (a -> b -> c, [s]) -> Parser st (a -> b -> c)
biOp (semantic, s) = biOp' semantic (pure_token s)

biOp' :: (a -> b -> c) -> Parser st d -> Parser st (a -> b -> c)
biOp' semantic biOp_reader = semantic <$ biOp_reader

anyBiOp :: (Show s, Describes s a', Provides st s a' pos) => [(a -> b -> c, [s])] -> Parser st (a -> b -> c)
anyBiOp = choice . (map biOp)

-- Number --

digit :: (Describes Char a, Provides st Char a pos) => Parser st a
digit = choice (map symSpaces "0123456789")

num :: (Provides st Char Int pos) => Parser st Int
num = (\x -> x) <$> digit

natural :: (Provides st Char Int pos) => Parser st Int
natural = (foldl (\a b -> a * 10 + b) 0) <$> many1 num

integer :: (Provides st Char Int pos) => Parser st Int
integer = integer' (token "-")

integer' :: (Provides st Char Int pos) => Parser st a -> Parser st Int
integer' negTok = (negate <$ negTok `opt` id) <*> natural

addSubtrOps :: (Describes Char a', Provides st Char a' pos) => Parser st (Int -> Int -> Int)
addSubtrOps = anyBiOp [((+), "+"), ((-), "-")]

multDivOps :: (Describes Char a', Provides st Char a' pos) => Parser st (Int -> Int -> Int)
multDivOps = anyBiOp [((*), "*")]


instance Describes Char Int where
    eqSymTok c n = fromEnum c - fromEnum '0' == n 
