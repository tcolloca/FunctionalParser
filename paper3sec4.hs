{-# LANGUAGE TransformListComp, MonadComprehensions, TupleSections, FunctionalDependencies #-}

import Data.Char (isSpace, isLetter, isAlphaNum)
import Control.Monad (MonadPlus(..), ap, liftM)
import Control.Applicative (Applicative(..), Alternative, empty, (<|>))
import Data.Functor (Functor(..), (<$>))

infixr 3 `opt`

-- Classes --

class symbol `Describes` token where
    eqSymTok :: symbol -> token -> Bool

class Symbol p symbol token where
    sym :: symbol -> p token

class Provides state symbol token | state symbol -> token where
    splitState :: symbol -> state -> Maybe (token, state)

class Eof state where
    eof :: state -> Bool

class ParserClass p where
    parse :: p state a -> state -> a

-- Parser definition --

newtype Parser s t = Parser ([s] -> Maybe (t, [s]))

    -- Instances --

instance Applicative (Parser s) where
    -- (<*>) :: Parser s (a -> b) -> Parser s a -> Parser s b
    p1 <*> p2 = [fr r2 | fr <- p1, r2 <- p2]

    -- (<.) :: Parser s a -> Parser s b -> Parser s a
    -- p1 <. p2 = const <$> p1 <*> p2

    -- (.>) :: Parser s a -> Parser s b -> Parser s b
    -- p1 .> p2 = id <$ p1 <*> p2 
    
    pure = return

instance Functor (Parser s) where
    -- (<$>) :: (a -> b) -> Parser s a -> Parser s b
    f `fmap` p = return f <*> p
    
    -- (<$) :: (b -> c) -> Parser s a -> Parser s (b -> c)
    -- f <$ p = const <$> return f <*> p

instance Monad (Parser s) where
    -- return :: a -> Parser s a
    return r = Parser (\inp -> return (r, inp))
    
    (Parser p) >>= f = Parser (\inp -> [(r', out') | (r, out) <- p inp,
                                                     let (Parser p') = f r,
                                                     (r', out') <- p' out])           

instance Alternative (Parser s) where
    -- (<|>) :: Parser s a -> Parser s a -> Parser s a 
    (Parser p1) <|> (Parser p2) = Parser (\s -> (p1 s) <|> (p2 s))
    
    -- empty :: Parser s a 
    empty = Parser (\s -> empty) 

    -- Run helper --

run :: Parser Char a -> String -> Maybe (a, String)
run (Parser p) str = p (f str) where 
    f (x:xs) = if isSpace x then f xs else x : (f xs)
    f [] = empty 

-- Basic parsers --

satisfy :: (s -> Bool) -> Parser s s
satisfy pred = Parser (\inp -> case inp of
                    (x:xs) | pred x -> return (x, xs)
                    otherwise -> empty)

epsilon :: Parser s t
epsilon = Parser (const empty)

symbol :: Eq a => a -> Parser a a
symbol c = satisfy (== c)

token :: Eq a => [a] -> Parser a [a]
token (x:xs) = symbol x <:*> token xs
token [] = return []

-- Parser combinators --
    
    -- Sequencing --

(<**>) :: Parser s a -> Parser s (a -> b) -> Parser s b
p1 <**> p2 = (\a f -> f a) <$> p1 <*> p2

(<:*>) :: Parser s a -> Parser s [a] -> Parser s [a]
p <:*> ps = (:) <$> p <*> ps

(<??>) :: Parser s a -> Parser s (a -> a) -> Parser s a
p1 <??> p2 = p1 <**> (p2 `opt` id)

    -- Choice / Branching --

opt :: Parser s a -> a -> Parser s a
p `opt` v = p <|> return v

    -- Iteration --

many :: Parser s a -> Parser s [a]
many p = p <:*> many p `opt` []

many1 :: Parser s a -> Parser s [a]
many1 p = p <:*> many p

chainl :: Parser s (a -> a -> a) -> Parser s a -> Parser s a
chainl op p = applyAll <$> p <*> many (flip <$> op <*> p) 

chainr :: Parser s (a -> a -> a) -> Parser s a -> Parser s a
chainr op p = r where r = p <??> (flip <$> op <*> r)

choice :: [Parser s a] -> Parser s a
choice = foldr (<|>) epsilon

seqnc :: [Parser s a] -> Parser s [a]
seqnc (p:ps) = p <:*> seqnc ps
seqnc [] = return []

    -- Packing --

pack :: Eq s => [s] -> Parser s a -> [s] -> Parser s a
pack open p close = token open *> p <* token close

parens :: Parser Char a -> Parser Char a
parens p = pack "(" p ")"

brackets :: Parser Char a -> Parser Char a
brackets p = pack "[" p "]"

curly :: Parser Char a -> Parser Char a
curly p = pack "{" p "}"

tagged :: Parser Char a -> Parser Char a
tagged p = pack "<" p ">"

-- String parsers --

letter :: Parser Char Char
letter = satisfy isLetter

word :: Parser Char String
word = many1 letter

-- Number --

digit :: Parser Char Char
digit = satisfy (\x -> x >= '0' && x <= '9')

num :: Parser Char Int
num = (\x -> fromEnum x - fromEnum '0') <$> digit

natural :: Parser Char Int
natural = (foldl (\a b -> a * 10 + b) 0) <$> many1 num

integer :: Parser Char Int
integer = (negate <$ token "-" `opt` id) <*> natural

op :: Eq s => (a -> b -> c, [s]) -> Parser s (a -> b -> c)
op (semantic, s) = semantic <$ token s

anyOp :: Eq s => [(a -> b -> c, [s])] -> Parser s (a -> b -> c)
anyOp = choice . (map op)

addSubtrOps :: Parser Char (Int -> Int -> Int)
addSubtrOps = anyOp [((+), "+"), ((-), "-")]

multDivOps :: Parser Char (Int -> Int -> Int)
multDivOps = anyOp [((*), "*")]

numFactor :: Parser Char Int
numFactor = integer <|> (parens numExpr)

numExpr :: Parser Char Int
numExpr = foldr chainl numFactor [addSubtrOps, multDivOps]

expr :: Parser Char Int
expr = numExpr <|> ifElse

-- Conditionals --

ifElse :: Parser Char Int
ifElse = (\bool a b -> if bool then a else b) <$ 
        token "if" <*> parens boolExpr <*> 
            expr <* 
        token "else" <*> 
            expr   

andOps :: Parser Char (Bool -> Bool -> Bool)
andOps = anyOp (map ((&&),) ["&&", "and"])

orOps :: Parser Char (Bool -> Bool -> Bool)
orOps = anyOp (map ((||),) ["||", "or"])

boolExpr :: Parser Char Bool
boolExpr = foldr chainl relExpr [andOps, orOps]

relOps :: Parser Char (Int -> Int -> Bool) 
relOps = anyOp [((<=), "<="), ((>=), ">="), ((<), "<"), ((>), ">")]
-- TODO : Add others

relExpr :: Parser Char Bool
relExpr = 
    const False <$> token "false" <|>
    const True <$> token "true" <|>
    expr <**> relOps <*> expr 

-- Utils --

applyAll :: a -> [a -> a] -> a
applyAll x (yf:yfs) = applyAll (yf x) yfs
applyAll x [] = x

-- Testing --

data Token = Identifier -- terminal symbol used in parser
           | Ident String -- token constructed by scanner
           | Number Int
           | If_Symbol
           | Then_Symbol



instance Eq Token where
    (Ident _) == Identifier = True

ident = symbol Identifier

doubleA :: Parser Char String
doubleA = (\c1 c2 -> [c1, c2]) <$> symbol 'a' <*> symbol 'a'

parensH :: Parser Char Int
parensH = (max .(1+)) <$> parens parensH <*> parensH `opt` 0

    -- XML --

data Xml = Tag XmlIdent [Xml] | Leaf String deriving Show
type XmlIdent = String

xmlIdent :: Parser Char XmlIdent
xmlIdent = word

xmlContent :: Parser Char String
xmlContent = many1 (satisfy isAlphaNum)

openTag :: Parser Char XmlIdent
openTag = tagged xmlIdent

closeTag :: XmlIdent -> Parser Char XmlIdent
closeTag t = tagged (symbol '/' *> token t)

emptyTag :: Parser Char Xml
emptyTag = flip Tag [] <$> tagged (xmlIdent <* symbol '/')

parseXml :: Parser Char Xml
parseXml = [Tag t subt | t <- openTag,
                         subt <- many parseXml,
                         _ <- closeTag t]
           <|> emptyTag
           <|> (Leaf <$> xmlContent)



