import Control.Monad.State
import Prelude hiding ((<*>), (<|>), (<$>), (<*), (*>), pure)

evenN :: Int -> [Int]
evenN n = [x | x <- [1..], x < n]

sumAndDouble :: Int ->Int -> Int
sumAndDouble x y = double x + double y

double :: Int -> Int
double x = x * 2

sum :: Int -> Int -> Int
sum x y = x + y

sumAndDoubleCps :: Int -> Int -> (Int -> r) -> r
sumAndDoubleCps x y = \ k ->
    doubleCps x                 (\ doubledX ->
    doubleCps y                 (\ doubledY ->
    sumCps    doubledX doubledY (\ doubleXplusDoubleY ->
    k        doubleXplusDoubleY))) 


doubleCps :: Int -> (Int -> r) -> r
doubleCps x = \ k -> k  (x * 2)

sumCps :: Int -> Int -> (Int -> r) -> r
sumCps x y = \ k -> k (x + y)

infixl 7 <$> 
infixl 5 <*> 
infixr 3 <|>

newtype Parser s r = P ([s] -> [(r, [s])])

unP :: Parser s r -> ([s] -> [(r, [s])])
unP (P p) = p


item :: Eq s => s -> Parser s s
item s = P (\ inp -> case inp of
                     (x:xs) | s == x -> [(x, xs)]
                     otherwise       -> [])   

pure :: r -> Parser s r
pure r = P (\ inp -> [(r, inp)])

empty :: Parser s r
empty  = P (\ inp -> [])

(<*^>) :: Parser s a -> Parser s b -> Parser s (a, b)
p <*^> q = P (\ inp -> [((r1, r2), out') | (r1, out ) <- unP p inp
                                         , (r2, out') <- unP q out]) 


(<*>) :: Parser s (b -> a) -> Parser s b -> Parser s a
p <*> q = P (\ inp -> [(r1 r2, out') | (r1, out)  <- unP p inp
                                     , (r2, out') <- unP q out])  


(<|>) :: Parser s a -> Parser s a -> Parser s a
p <|> q = P (\ inp -> unP p inp ++ unP q inp)  

opt :: Parser s a -> a -> Parser s a
p `opt` v = p <|> pure v


(<$>) :: (a -> b) -> Parser s a -> Parser s b
f <$> p = pure f <*> p 


token' :: Eq s => [s] -> Parser s [s]
token' (x:xs) = (:) <$> item x <*> token' xs
token'     [] = pure [] 

infixr 5 <:*>

(<:*>) :: Parser s a -> Parser s [a] -> Parser s [a]
p <:*> q = (:) <$> p <*> q

token :: Eq s => [s] -> Parser s [s]
token (x:xs) = item x <:*> token xs
token []     = pure [] 

infixl 5 <*, *>

(*>) :: Parser s a -> Parser s b -> Parser s b
p *> q = flip const <$> p <*> q 

(<*) :: Parser s a -> Parser s b -> Parser s a
p <* q = const <$> p <*> q 

parens :: Parser Char a -> Parser Char a 
parens p = token "(" *> p <* token ")"

pack :: Parser s b -> Parser s a -> Parser s c -> Parser s a 
pack open p close = open *> p <* close

choice :: [Parser s a] -> Parser s a
choice ps = foldr (<|>) empty ps

digit :: Parser Char Char
digit = choice (map item ['0'..'9'])

lowercase :: Parser Char Char
lowercase = choice (map item ['a'..'z'])

uppercase :: Parser Char Char
uppercase = choice (map item ['A'..'Z'])

letter :: Parser Char Char
letter = lowercase <|> uppercase

alphaNum :: Parser Char Char
alphaNum = digit <|> letter


many :: Parser s a -> Parser s [a]
many p = p <:*> many p <|> pure []

many1 :: Parser s a -> Parser s [a]
many1 p = p <:*> many p


word :: Parser Char String
word = many1 letter

ident :: Parser Char String
ident = many1 alphaNum

intDigit :: Parser Char Int
intDigit = (\ x -> fromEnum x - fromEnum '0') <$> digit

nat :: Parser Char Int 
nat = (foldl (\a b -> a * 10 + b) 0) <$> many1 intDigit


infixl 7 <?|>

(<?|>) :: Parser s a -> (a -> b, b) -> Parser s b
p <?|> (f, z) = (f <$> p) <|> pure z 

int :: Parser Char Int
int = token "-" <?|> (const negate, id) <*> nat


sepBy1 :: Parser s a -> Parser s b -> Parser s [a]
sepBy1 p sep = p <:*> many (sep *> p)

sepBy :: Parser s a -> Parser s b -> Parser s [a]
sepBy p sep = sepBy1 p sep `opt` []

addTwo :: Parser Char Int
addTwo = (+) <$> int <* token "+" <*> int 


infixl 5 <**>

(<**>) :: Parser s a -> Parser s (a -> b) -> Parser s b
p <**> q = (\ a f -> f a) <$> p <*> q

opTwo :: Parser Char (Int -> Int -> Int) -> Parser Char Int
opTwo op  = int <**> op <*> int

add' :: Parser Char (Int -> Int -> Int)
add' = const (+) <$> token "+" 

biOp :: Eq s => (a -> b -> c, [s]) -> Parser s (a -> b -> c)
biOp (f, tok) = const f <$> token tok 

add :: Parser Char (Int -> Int -> Int)
add = biOp ((+), "+") 


opFour' :: Parser Char (Int -> Int -> Int) -> Parser Char Int
opFour' op = (((int <**> (op <*> int)) <**> (op <*> int)) <**> (op <*> int))



applyAll :: a -> [a -> a] -> a
applyAll z (f:fs) = applyAll (f z) fs
applyAll z [] = z

opFour'' :: Parser Char (Int -> Int -> Int) -> Parser Char Int
opFour'' op = applyAll <$> int <*> many (flip <$> op <*> int)

chainl :: Parser s (a -> a -> a) -> Parser s a -> Parser s a
chainl op p = applyAll <$> p <*> many (flip <$> op <*> p)

chainr' :: Parser s (a -> a -> a) -> Parser s a -> Parser s a
chainr' op p = p <|> p <**> (flip <$> op <*> chainr' op p)


(<??>) :: Parser s a -> Parser s (a -> a) -> Parser s a
p1 <??> p2 = p1 <**> (p2 `opt` id)

chainr :: Parser s (a -> a -> a) -> Parser s a -> Parser s a
chainr op p = p <??> (flip <$> op <*> chainr op p)
