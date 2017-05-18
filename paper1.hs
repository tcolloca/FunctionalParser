import Data.Char (ord, isDigit)
import Data.List

type Parser symbol result = [symbol] -> [([symbol], result)]
type DetParser symbol result = [symbol] -> result

data Tree = Nil | Bin (Tree,Tree) deriving Show

infixr 6 <.>, <., .>
infixr 5 <@, <?@
infixr 4 <|>

-- Basic Functions --

power :: Fractional a => Int -> a
power e | e < 0 = 1.0 / power (-e)
        | otherwise = fromIntegral 10^e

list :: (c, [c]) -> [c]
list (x, xs) = x:xs

ap :: (a -> b, a) -> b
ap (f, x) = f x

ap1 :: (a, a -> b -> c) -> b -> c 
ap1 (a, op) = (a `op`)

ap2 :: (a -> b -> c, b) -> a -> c 
ap2 (op, y) = (`op` y)

-- Elementary Parsers --

symbol :: Eq a => a -> Parser a a
symbol c s = satisfy (c ==) s

token :: Eq a => [a] -> Parser a [a]
token = sequenced . (map symbol)

satisfy :: (a -> Bool) -> Parser a a
satisfy p [] = []
satisfy p (x:xs) = [(xs, x) | p x]

succeed :: r -> Parser a r
succeed r s = [(s, r)]

epsilon :: Parser a ()
epsilon = succeed ()

none :: Parser a r
none s = []

-- Numbers --

digit :: Parser Char Int
digit = satisfy isDigit <@ f
               where f x = ord x - ord '0'

natural :: Parser Char Int
natural = many1 digit <@ foldl f 0
          where f a b = a * 10 + b 

integer :: Parser Char Int
integer = (option (symbol '-') <?@ (id, const negate)) 
          <.> 
          natural 
          <@ ap     

fract :: Parser Char Float
fract = many1 digit <@ foldr f 0.0
        where f a b = (b + fromIntegral a) / 10.0

fixed :: Parser Char Float
fixed = ((option (symbol '-') <?@ (id, const negate)) 
        <.> 
        (((option natural <?@ (0, fromIntegral))
        <.> 
        (option (symbol '.' .> fract) <?@ (0.0, id))) 
        <@ uncurry (+))
        <@ ap)
        <~>
        (epsilon <@ const 0)

float :: Parser Char Float
float = fixed
        <.>
        (option (((symbol 'e') <|> (symbol 'E')) .> integer) <?@ (0, id))
        <@ f
        where f (m,e) = m * power e         

-- Enclosed --

parenthesized, bracketed, curlybracketed :: Parser Char r -> Parser Char r
parenthesized p = pack (symbol '(') p (symbol ')')
bracketed p = pack (symbol '[') p (symbol ']')
curlybracketed p = pack (symbol '{') p (symbol '}')

-- Lists --

commaList, semicList, enterList :: Parser Char a -> Parser Char [a]
commaList p = listOf p (symbol ',')
semicList p = listOf p (symbol ';')
enterList p = listOf p (symbol '\n')

-- Parens --

open :: Parser Char Char
open = symbol '('

close :: Parser Char Char
close = symbol ')'

parens :: Parser Char Tree
parens = foldParens Bin Nil

nesting :: Parser Char Int
nesting = foldParens f 0 where f (x, y) = max (x + 1) y

foldParens :: ((r, r) -> r) -> r -> Parser Char r
foldParens f z = pack open (foldParens f z) close <.> (foldParens f z) <@ f
         <|> succeed z

treeToParens :: Tree -> String
treeToParens Nil = ""
treeToParens (Bin (t1, t2)) = "(" ++ (treeToParens t1) ++ ")" ++ (treeToParens t2) 

-- Parser Combinators --

(<.>) :: Parser a r -> Parser a s -> Parser a (r,s)
(p1 <.> p2) s = [(xs2, (r1, r2))
                | (xs1, r1) <- p1 s
                , (xs2, r2)<- p2 xs1]

(<.) :: Parser a r -> Parser a s -> Parser a r
p1 <. p2 = p1 <.> p2 <@ fst

(.>) :: Parser a r -> Parser a s -> Parser a s
p1 .> p2 = p1 <.> p2 <@ snd

(<:.>) :: Parser a r -> Parser a [r] -> Parser a [r]
p1 <:.> p2 = p1 <.> p2 <@ list

(<|>) :: Parser a r -> Parser a r -> Parser a r
(p1 <|> p2) s = p1 s ++ p2 s

(<~>) :: (Eq a, Eq r) => Parser a r -> Parser a r -> Parser a r
(p1 <~> p2) s = p1 s \\ p2 s  

-- Parser Transformers --

negl :: Eq a => a -> Parser a r -> Parser a r
negl a p = p . dropWhile (== a)

just :: Parser a r -> Parser a r
just p xs = [([], r) 
            | (ys, r) <- p xs
            , null ys]

(<@) :: Parser a r -> (r -> s) -> Parser a s
(p <@ f) s = [(xs, f r) | (xs, r) <- p s]

(<?@) :: Parser a [r] -> (v, r -> v) -> Parser a v
p <?@ (z, f) = p <@ g
               where g [] = z
                     g [x] = f x

some :: Parser a r -> DetParser a r
some p = snd . head . just p

many :: Parser a r -> Parser a [r]
many p = p <:.> many p
         <|> succeed []

many1 :: Parser a r -> Parser a [r]
many1 p = p <:.> many p

option :: Parser a r -> Parser a [r]
option p = p <@ (\x -> [x])
           <|> succeed []

pack :: Parser a r1 -> Parser a r2 -> Parser a r3 -> Parser a r2
pack s1 p s2 = s1 .> p <. s2

listOf :: Parser a r1 -> Parser a r2 -> Parser a [r1]
listOf p s = p <:.> many (s .> p) <|> succeed []

sequenced :: [Parser a r] -> Parser a [r]
sequenced = foldr (<:.>) (succeed [])

choice :: [Parser a r] -> Parser a r
choice = foldr (<|>) none

chainl :: Parser s a -> Parser s (a -> a -> a) -> Parser s a
chainl p s = p <.> many (s <.> p) <@ uncurry (foldl (flip ap2))

-- chainr' p s = q
-- where q = p <*> (option (s <*> q) <?@ (id,ap2) )
-- <@ flip ap

chainr :: Parser s a -> Parser s (a -> a -> a) -> Parser s a
chainr p s = many (p <.> s) <.> p <@ uncurry (flip (foldr ap1)) 

first :: Parser a b -> Parser a b
first p xs | null r = []
           | otherwise = [head r]
           where r = p xs

greedy :: Parser a b -> Parser a [b]
greedy = first . many

greedy1 :: Parser a b -> Parser a [b]
greedy1 = first . many1

compulsion :: Parser a b -> Parser a [b]
compulsion = first . option
