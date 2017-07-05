{-# LANGUAGE TransformListComp, MonadComprehensions, TupleSections, FunctionalDependencies, GADTs,
ExistentialQuantification, Rank2Types, TypeOperators, FlexibleInstances #-}

import Data.Char (isSpace, isLetter, isAlphaNum)
import Control.Monad (MonadPlus(..), ap, liftM)
import Control.Applicative (Applicative(..), Alternative, empty, (<|>))
import Data.Functor (Functor(..), (<$>))

infixr 3 `opt`

-- test --

data Str = Str {input :: String}

listToStr :: String -> Str
listToStr ls = Str ls    

instance Describes Char Char where
    eqSymTok sym tok = sym == tok

instance Provides Str Char Char where
    splitState _ (Str []) = Nothing
    splitState _ (Str (t:ts)) = Just (t, Str ts)

instance Eof Str where
    eof (Str l) = null l

tom = (sym 'a') :: (Pm Str Char)

tom' = ((\a b -> [a, b]) <$> (sym 'a' <|> sym 'c') <*> sym 'b') :: (Pm Str [Char])

-- Classes --

class symbol `Describes` token where
    eqSymTok :: symbol -> token -> Bool

class Symbol p symbol token where
    sym :: symbol -> p token

-- state symbol Provides token
class Provides state symbol token | state symbol -> token where
    splitState :: symbol -> state -> Maybe (token, state)

class Eof state where
    eof :: state -> Bool

class ParserClass p state where
    parse :: p state a -> state -> a

data Steps a where
    Step :: Steps a -> Steps a
    Fail :: Steps a
    Apply :: (b -> a) -> Steps b -> Steps a
    Success :: Steps a -> Steps a

stepsDone :: a -> Steps a
stepsDone a = Apply (const a) Fail

eval :: Steps a -> a
eval (Apply f v) = f (eval v)
eval (Step l) = eval l
eval Fail = error "should not happen"

norm :: Steps a -> Steps a
norm (Apply f (Apply g l)) = norm (Apply (f . g) l)
norm (Apply f (Step l)) = Step (Apply f l)
norm (Apply f Fail) = Fail
norm steps = steps

best :: Steps a -> Steps a -> Steps a
l `best` r = norm l `best'` norm r
    where Fail      `best'` r        = r
          l         `best'` Fail     = l
          (Step l)  `best'` (Step r) = Step (l `best` r)
          _         `best'` _        = Fail -- Ambiguous

class Greedy p where
    (<<|>) :: p a -> p a -> p a

best_gr :: Steps a -> Steps a -> Steps a
l@(Step _) `best_gr` _ = l
l `best_gr` r = l `best` r

-- Recognizer --

newtype R st a = R (forall r. (st -> Steps r) -> st -> Steps r)

instance ((symbol `Describes` token), (Provides state symbol token))
    => Symbol (R state) symbol token where
    sym a = R (\k st -> case splitState a st of
                            Just (t, ss) -> if a `eqSymTok` t
                                                then Step (k ss)
                                                else Fail
                            Nothing -> Fail) 

-- History parser --

newtype Ph st a = Ph (forall r. (a -> st -> Steps r) -> st -> Steps r)

unPh (Ph p) = p

instance Applicative (Ph st) where
    -- (<*>) :: Ph st (a -> b) -> Ph st a -> Ph st b
    (Ph p) <*> (Ph q) = Ph (\k -> p (\f -> q (\a -> k (f a))))
    -- return --
    pure = return

instance Functor (Ph st) where
    --(<$>) :: (b -> a) -> Ph st b -> Ph st a
    f `fmap` (Ph p) = Ph (\k -> p (\a -> k (f a)))

instance Monad (Ph st) where
    (Ph p) >>= a2q = Ph (\k -> p (\a -> unPh (a2q a) k))       
    -- return :: a -> Ph st a
    return r = Ph (\k -> k r)

instance Alternative (Ph st) where
    --(<|>) :: Ph st a -> Ph st b -> Ph st a
    (Ph p1) <|> (Ph p2) = Ph (\k inp -> p1 k inp `best` p2 k inp)    
    -- empty :: Ph st a
    empty = Ph (\k -> const Fail)

instance ((symbol `Describes` token), (Provides state symbol token))
    => Symbol (Ph state) symbol token where
        -- symbol -> p token
        sym a = Ph (\k st -> case splitState a st of
                                Just (t, ss) -> if eqSymTok a t 
                                                    then Step (k t ss)
                                                    else Fail
                                Nothing -> Fail)

instance Eof state => ParserClass Ph state where
    parse (Ph p) st = (eval . p (\r rest -> if eof rest
                                                then stepsDone r 
                                                else Fail)) st

instance Greedy (Ph st) where
    Ph p <<|> Ph q = Ph (\k st -> p k st `best_gr` q k st)

-- Future parser --

newtype Pf st a = Pf (forall r. (st -> Steps r) -> st -> Steps (a, r))

unPf (Pf p) = p

instance Applicative (Pf st) where
    -- (<*>) :: Pf st (a -> b) -> Pf st a -> Pf st b
    (Pf p) <*> (Pf q) = Pf (\k st -> applyf (p (q k) st))
    -- return --
    pure = return

instance Functor (Pf st) where
    --(<@>) :: (b -> a) -> Ph st b -> Ph st a
    f `fmap` p = return f <*> p

instance Monad (Pf st) where
    (Pf p) >>= pv2q = Pf (\k st ->
                        let steps = p (q k) st
                            q = unPf (pv2q pv)
                            pv = fst (eval steps)
                        in Apply snd steps)  
    -- return :: a -> Pf st a
    return a = Pf (\k st -> push a (k st))

instance Alternative (Pf st) where
    --(<|>) :: Pf st a -> Pf st b -> Pf st a
    (Pf p1) <|> (Pf p2) = Pf (\k st -> p1 k st `best` p2 k st)
    -- empty :: Pf st a
    empty = Pf (\_ -> const Fail)

push :: v -> Steps r -> Steps (v, r)
push v = Apply (\s -> (v, s))

applyf :: Steps (b -> a, (b, r)) -> Steps (a, r)
applyf = Apply (\(b2a, ~(b, r)) -> (b2a b, r))

instance ((symbol `Describes` token), (Provides state symbol token))
    => Symbol (Pf state) symbol token where
        -- symbol -> p token
        sym a = Pf (\k st -> case splitState a st of
                                Just (t, ss) -> if eqSymTok a t 
                                                    then Step (push t (k ss))
                                                    else Fail
                                Nothing -> Fail)

instance Eof state => ParserClass Pf state where
    parse (Pf p) st = (fst . eval . p (\st -> if eof st
                                                then undefined 
                                                else error "end")) st

instance Greedy (Pf st) where
    Pf p <<|> Pf q = Pf (\k st -> p k st `best_gr` q k st)

-- Monadic parser --

data Pm state a = Pm (Ph state a) (Pf state a)

unPm_h (Pm (Ph h) _) = h
unPm_f (Pm _ (Pf f)) = f

instance Applicative (Pm st) where
    -- (<*>) :: Pm st (a -> b) -> Pm st a -> Pm st b
    (Pm hp fp) <*> ~(Pm hq fq) = Pm (hp <*> hq) (fp <*> fq)
    -- return --
    pure = return

instance Functor (Pm st) where
    --(<@>) :: (b -> a) -> Pm st b -> Pm st a
    f `fmap` p = return f <*> p

instance Monad (Pm st) where
    (Pm (Ph p) _) >>= a2q = Pm 
        (Ph (\k -> p (\a -> unPm_h (a2q a) k)))
        (Pf (\k -> p (\a -> unPm_f (a2q a) k)))
    -- return :: a -> Pm st a
    return a = Pm (return a) (return a)

instance Alternative (Pm st) where
    --(<|>) :: Pm st a -> Pm st b -> Pm st a
    (Pm hp fp) <|> (Pm hq fq) = Pm (hp <|> hq) (fp <|> fq)
    -- empty :: Pm st a
    empty = Pm empty empty

instance ((symbol `Describes` token), (Provides state symbol token))
    => Symbol (Pm state) symbol token where
    sym a = Pm (sym a) (sym a)

instance Eof state => ParserClass Pm state where
    parse (Pm _ (Pf fp)) = fst . eval . fp (\rest -> if eof rest
                                                        then undefined
                                                        else error "parse")

instance Greedy (Pm st) where
    Pm ph pf <<|> Pm qh qf = Pm (ph <<|> qh) (pf <<|> qf)

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
choice = foldr (<|>) empty

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



