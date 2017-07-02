{-# LANGUAGE TransformListComp, MonadComprehensions #-}

import Control.Monad (MonadPlus(..), mzero, ap, liftM)
import Control.Applicative ((<|>), Alternative, empty)
import Control.Monad.State (StateT(..))
import Control.Monad.Reader (ReaderT(..), ask, local)
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

instance StateMonad m a => StateMonad (ReaderT s m) a where 
    -- update :: StateMonad m a => (a -> a) -> ReaderT s m a
    update f = ReaderT (\_ -> update f)

type Pos = (Int, Int)

type Pstring = (Pos, String)

type Parser a = ReaderT Pos (StateT Pstring Maybe) a


-- -- Parser combintators --

-- (<.>) :: Parser a -> Parser b -> Parser (a,b)
-- p <.> q = StateT (\s -> [((v, w), xs2) 
--                   | (v, xs1) <- runStateT p s
--                   , (w, xs2) <- runStateT q xs1])

(+++) :: Parser a -> Parser a -> Parser a
p +++ q = first (p <|> q)

-- first :: Parser a -> Parser a
-- first p = ReaderT (\pos -> StateT (\str -> case (runStateT ((runReaderT p) pos)) str of
--       [] -> []
--       (x:xs) -> [x]))

first :: Parser a -> Parser a
first p = p

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
item = [x | (pos,x:_) <- update newstate
        , defpos <- ask
        , onside pos defpos]

onside :: Pos -> Pos -> Bool
onside (l,c) (dl,dc) = (c > dc) || (l == dl)

tabsize :: Int
tabsize = 8

newstate :: Pstring -> Pstring
newstate ((l,c),x:xs) = (newpos,xs) where 
      newpos = case x of
            '\n' -> (l+1,0)
            '\t' -> (l,((c `div` tabsize)+1)*tabsize)
            _ -> (l,c+1)

junk :: Parser ()
junk = [() | _ <- local (const (0,-1)) (many (spaces +++ comment))]

many1_offside :: Parser a -> Parser [a]
many1_offside p = [vs | (pos, _) <- update id :: Parser Pstring
                      , vs <- local (const pos) (many1 (off p))]

off :: Parser a -> Parser a
off p = [v | (dl,dc) <- ask
            , ((l,c), _) <- update id :: Parser Pstring
            , c == dc
            , v <- local (const (l,dc)) p]

many_offside :: Parser a -> Parser [a]
many_offside p = many1_offside p +++ mzero

---

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

identifier :: [String] -> Parser String
identifier ks = token [x | x <- iden, not (elem x ks)]

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


-- Lambda expressions --

data Expr = App Expr Expr -- application
          | Lam String Expr -- lambda abstraction
          | Let [(String,Expr)] Expr -- local definition
          | Var String -- variable
          deriving Show

lamexpr = atom `chainl1` (return App)

atom = lam +++ localdef +++ var +++ paren

lam = [Lam x e | _ <- symbol "\\"
              , x <- variable
              , _ <- symbol "->"
              , e <- lamexpr]

localdef = [Let ds e | _ <- symbol "let"
                    , ds <- many1_offside defn
                    , _ <- symbol "in"
                    , e <- lamexpr]

defn = [(x, e) | x <- identifier []
              , _ <- symbol "="
              , e <- lamexpr]

var = [Var x | x <- variable]

paren = pack (symbol "(") lamexpr (symbol ")")

variable = identifier ["let", "in"]

runParser :: Parser a -> String -> Maybe (a, Pstring)
runParser p inp = (runStateT ((runReaderT p) (0,0))) ((0,0), inp)
