{-# LANGUAGE TransformListComp, MonadComprehensions #-}

import Control.Monad (MonadPlus(..), mzero, ap, liftM)
import Control.Applicative ((<|>), Alternative, empty)
import Control.Monad.State (StateT(..))
import Data.Monoid (Product)
import Data.Char (ord)

-- data Complex a = Complex [(a, a)] | Simple ()

-- instance Show a => Show (Complex a) where
--     show (Complex b) = show b
--     show (Simple ()) = show ()

-- instance Applicative Complex where
--     pure  = return
--     (<*>) = ap

-- instance Functor Complex where
--     fmap  = liftM

-- instance Alternative Complex where
--     (<|>) = mplus
--     empty = mzero 

-- instance Monad Complex where
--     return v = Complex [(v, v)]
--     (Complex v) >>= f = (f . fst . head) v
--     (Simple ()) >>= f = Simple ()

-- instance MonadPlus Complex where
--     mzero = Simple ()
--     (Complex a) `mplus` (Complex b) = Complex (a `mplus` b)
--     (Complex a) `mplus` _ = Complex a
--     _ `mplus` (Complex b) = Complex b
--     _ `mplus` _ = Simple ()

data Numeric a = Num (a, Int) | Void deriving Show

class Monad m => StateMonad m s where
  update :: (s -> s) -> m s
  
  set :: s -> m s
  set s = update (\_ -> s)
  
  fetch :: m s
  fetch = update id

instance Applicative Numeric where
    pure  = return
    (<*>) = ap

instance Functor Numeric where
    fmap  = liftM

instance Alternative Numeric where
    (<|>) = mplus
    empty = mzero 

instance Monad Numeric where
    return v = Num (v, 1)
    Num (a, _) >>= f = f a
    Void >>= f = Void

instance MonadPlus Numeric where
    mzero = Void
    (Num (a, b)) `mplus` (Num (c, d)) = Num (a, b + d)
    (Num (a, b)) `mplus` _ = Num (a, b)
    _ `mplus` (Num (a, b)) = Num (a, b)
    _ `mplus` _ = Void

instance Monad m => StateMonad (StateT s m) s where 
    -- update :: Monad m => (s -> s) -> StateT s m s
    update f = StateT (\s -> return (s, f s))

type Parser a = StateT String [] a


-- Parser combintators --

(<.>) :: Parser a -> Parser b -> Parser (a,b)
p <.> q = StateT (\s -> [((v, w), xs2) 
                  | (v, xs1) <- runStateT p s
                  , (w, xs2) <- runStateT q xs1])

-- Parser Transformers --

many :: Parser a -> Parser [a]
many p = [x:xs | x <- p, xs <- many p] <|> return []

many1 :: Parser a -> Parser [a]
many1 p = do {x <- p; xs <- many p; return (x:xs)}

listOf :: Parser a -> Parser b -> Parser [a]
listOf p sep = [x:xs | x <- p, xs <- many [r | _ <- sep, r <- p]]

pack :: Parser a -> Parser b -> Parser c -> Parser b
pack open p close = [x | _ <- open, x <- p, _ <- close]

ops :: [(Parser a, b)] -> Parser b
ops l = foldr1 (<|>) [[op | _ <- p] | (p, op) <- l]

chainl1 :: Parser a -> Parser (a -> a -> a) -> Parser a
chainl1 p op = p >>= rest where
                     rest x = (op >>= \f ->
                               p >>= \y ->
                               rest (f x y)) <|> return x

chainr1 :: Parser a -> Parser (a -> a -> a) -> Parser a
chainr1 p op = p >>= (\x -> [f x y | f <- op, y <- chainr1 p op] <|> return x)

chainl :: Parser a -> Parser (a -> a -> a) -> a -> Parser a
chainl p op v = (chainl1 p op) <|> return v

chainr :: Parser a -> Parser (a -> a -> a) -> a -> Parser a
chainr p op v = (chainr1 p op) <|> return v

-- Basic Functions --

ap1 :: a -> ((a -> b -> c), b) -> c
ap1 x (f, y) = f x y

ap2 :: b -> (a, (a -> b -> c)) -> c
ap2 y (x, f) = f x y

-- Elementary Parsers --

item :: Parser Char
item = [x | (x:_) <- update tail]

sat :: (Char -> Bool) -> Parser Char
sat p = item >>= \x ->
        if p x then return x else mzero

-- Ignore Parsers --

spaces :: Parser ()
spaces = [() | _ <- many1 (sat isSpace)] where
            isSpace x = (x == ' ') || (x == '\n') || (x == '\t')

singlecomment :: Parser ()
singlecomment = [() | _ <- string "--", _ <- many (sat (\x -> x /= '\n'))]

multicomment :: Parser ()
multicomment = [() | _ <- string "{-", _ <- many item, _ <- string "-}"]

comment :: Parser ()
comment = singlecomment <|> multicomment

junk :: Parser ()
junk = [() | _ <- many (spaces <|> comment)]

prepare :: Parser a -> Parser a
prepare p = [v | _ <- junk, v <- p]

token :: Parser a -> Parser a
token p = [v | v <- p, _ <- junk]

-- String Parsers --

char :: Char -> Parser Char
char x = sat (\y -> x == y)

digit :: Parser Char
digit = sat (\x -> '0' <= x && x <= '9')

digits :: Parser String
digits = many digit

sp :: Parser String
sp = many (char ' ')

lower :: Parser Char
lower = sat (\x -> 'a' <= x && x <= 'z')

upper :: Parser Char
upper = sat (\x -> 'A' <= x && x <= 'Z')

letter :: Parser Char
letter = lower <|> upper

alphanum :: Parser Char
alphanum = letter <|> digit

word :: Parser String
word =  many letter

iden :: Parser String
iden =  many1 alphanum

identifier :: Parser String
identifier = token iden

string :: String -> Parser String
string "" = return ""
string (x:xs) = do {r1 <- char x; r2 <- string xs; return (r1:r2)}

symbol :: String -> Parser String
symbol s = token (string s)

-- Numbers --

singleNum :: Parser Int
singleNum = do {r <- digit; return (ord r - ord '0')}

nat :: Parser Int
nat = chainl1 singleNum (return (\x y -> 10 * x + y))

natural :: Parser Int
natural = token nat

int :: Parser Int
int = [-n | _ <- char '-', n <- nat] <|> nat

integer :: Parser Int
integer = token int

test :: Parser Int
test = [x | _ <- char ',', x <- int]

ints :: Parser [Int]
ints = listOf int (char ',')

number :: Parser Int
number = nat <|> return 0

-- Arithmetic Expr --

addops :: Num a => Parser (a -> a -> a) 
addops = ops [(char '+', (+)), (char '-', (-))]

expops :: (Num a, Integral b) => Parser (a -> b -> a)
expops = ops [(char '^', (^))]

factor :: Parser Int
factor = int <|> pack (char '(') expr (char ')')

term :: Parser Int
term = chainr1 factor expops

expr :: Parser Int
expr = chainl1 term addops