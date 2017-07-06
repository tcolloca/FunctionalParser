{-# LANGUAGE TransformListComp, MonadComprehensions, TupleSections, FunctionalDependencies, GADTs,
ExistentialQuantification, Rank2Types, TypeOperators, FlexibleInstances, FlexibleContexts #-}

import Data.Char (isSpace, isLetter, isAlphaNum)
import Control.Monad (MonadPlus(..), ap, liftM)
import Control.Applicative hiding ((*>), (<*), many, (<**>), (<$))
import Data.Functor hiding ((<$))
import Prelude hiding ((<$), (<*), (*>))

infixr 3 `opt`

-- test --

data Str = Str {input :: String, pos :: Int}

listToStr :: String -> Str
listToStr ls = Str ls 0   

instance Describes Char Char where
    eqSymTok sym tok = sym == tok

instance Provides Str Char Char where
    splitState _ (Str [] _) = Nothing
    splitState _ (Str (t:ts) pos) = Just (pos + 1, t, Str ts (pos + 1))

instance Eof Str where
    eof (Str l _) = null l

syma = (sym 'a') :: (Pm Str Char)

symas = ((\a -> [a]) <$> syma) :: (Pm Str String)

symb = (sym 'b') :: (Pm Str Char)

tom' = ((\a b -> [a, b]) <$> (sym 'a' <|> sym 'c') <*> sym 'b') :: (Pm Str [Char])

-- tom'' = ((foldr (:) []) <$> many (sym 'a')) :: (Pm Str String)

-- test2 --

data Str2 = Str2 {input2 :: String, pos2 :: Int}

listToStr2 :: String -> Str2
listToStr2 ls = Str2 ls 0

instance Describes Char Int where
    eqSymTok c n = fromEnum c - fromEnum '0' == n 

instance Provides Str2 Char Int where
    splitState _ (Str2 [] _) = Nothing
    splitState _ (Str2 (t:ts) pos) = Just (pos + 1, fromEnum t - fromEnum '0', Str2 ts (pos + 1))

instance Eof Str2 where
    eof (Str2 l _) = null l

tomNum = (sym '0') :: (Pm Str2 Int)

-- Classes --

type Progress = Int

class symbol `Describes` token where
    eqSymTok :: symbol -> token -> Bool

class Symbol p symbol token where
    sym :: symbol -> p token

-- state symbol Provides token
class Provides state symbol token | state symbol -> token where
    splitState :: symbol -> state -> Maybe (Progress, token, state)

class Eof state where
    eof :: state -> Bool

class ParserClass p state where
    parse :: p state a -> state -> a

data Steps a where
    Step :: Progress -> Steps a -> Steps a
    Fail :: Steps a
    Done :: a -> Steps a
    Apply :: (b -> a) -> Steps b -> Steps a
    Success :: Steps a -> Steps a
    Endh :: ([a], [a] -> Steps r) -> Steps (a, r) -> Steps (a, r)
    Endf :: [Steps a] -> Steps a -> Steps a
    Micro :: Steps a -> Steps a

eval :: Steps a -> a
eval (Done a) = a
eval (Apply f v) = f (eval v)
eval (Step _ l) = eval l
eval Fail = error "should not happen"

norm :: Steps a -> Steps a 
norm (Apply f (Apply g l)) = norm (Apply (f . g) l)
norm (Apply f (Step n l)) = Step n (Apply f l)
norm (Apply f Fail) = Fail
norm steps = steps

best :: Steps a -> Steps a -> Steps a
l `best` r = norm l `best'` norm r
    where Fail      `best'` r        = r
          l         `best'` Fail     = l
          (Step n l)  `best'` (Step m r)
                        | n == m = Step n (l `best` r)
                        | n < m = Step n (l `best` Step (m - n) r)
                        | n > m = Step m (Step (n - m) l `best` r)
          Endh (as, k_st) l `best'` Endh (bs, _) r = Endh (as ++ bs, k_st) (l `best` r)
          Endh as l `best'` r = Endh as (l `best` r)
          l `best'` Endh bs r = Endh bs (l `best` r)
          (Micro l) `best'` r@(Step _ _) = r
          l@(Step _ _) `best'` (Micro _) = l
          (Micro l) `best'` (Micro r) = Micro (l `best` r)
          _         `best'` _        = Fail -- Ambiguous

class Greedy p where
    (<<|>) :: p a -> p a -> p a

best_gr :: Steps a -> Steps a -> Steps a
l@(Step _ _) `best_gr` _ = l
l `best_gr` r = l `best` r

class Ambiguous p where
    amb :: p a -> p [a]

class Micro p where
    micro :: p a -> p a

class Switch p where
    switch :: (st1 -> (st2, st2 -> st1)) -> p st2 a -> p st1 a

class ExtApplicative p st where
    (<*) :: p a -> R st b -> p a
    (*>) :: R st b -> p a -> p a
    (<$) :: a -> R st b -> p a

-- Recognizer --

newtype R st a = R (forall r. (st -> Steps r) -> st -> Steps r)

unR (R r) = r

instance Applicative (R st) where
    -- R st (a -> b) -> R st a -> R st b 
    (R r1) <*> (R r2) = R (\k st -> r1 (r2 k) st)
    -- return --
    pure = return

instance Functor (R st) where
    --(<$>) :: (b -> a) -> R st b -> R st a
    f `fmap` R r = R r

instance Monad (R st) where
    -- R st a -> (a -> R st b) -> R st b
    (R r) >>= f = R r    
    -- return :: a -> R st a
    return r = R (\k st -> k st)

instance Alternative (R st) where
    --(<|>) :: R st a -> R st b -> R st a
    (R r1) <|> (R r2) = R (\k inp -> r1 k inp `best` r2 k inp)    
    -- empty :: R st a
    empty = R (\k st -> Fail)

instance ((symbol `Describes` token), (Provides state symbol token))
    => Symbol (R state) symbol token where
    sym a = R (\k st -> case splitState a st of
                            Just (n, t, ss) -> if a `eqSymTok` t
                                                then Step n (k ss)
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
                                Just (n, t, ss) -> if eqSymTok a t 
                                                    then Step n (k t ss)
                                                    else Fail
                                Nothing -> Fail)

instance Eof state => ParserClass Ph state where
    parse (Ph p) st = (eval . p (\r rest -> if eof rest
                                                then Done r 
                                                else Fail)) st

instance Greedy (Ph st) where
    Ph p <<|> Ph q = Ph (\k st -> p k st `best_gr` q k st)

instance Ambiguous (Ph state) where
    amb (Ph p) = Ph (\k -> removeEndh . p (\a st' -> Endh ([a], \as -> k as st') Fail))

removeEndh :: Steps (a, r) -> Steps r
removeEndh Fail = Fail
removeEndh (Step n l) = Step n (removeEndh l)
removeEndh (Done (a, r)) = Done r
removeEndh (Apply f l) = error "no apply in history"
removeEndh (Endh (as, k_st) r) = k_st as `best` removeEndh r

instance Micro (Ph state) where
    micro (Ph p) = Ph ((Micro .) . p) -- TODO: Review

instance Switch Ph where
    switch split (Ph p) = Ph (\k st1 -> let (st2, st2tost1) = split st1
                                       in p (\a st2' -> k a (st2tost1 st2')) st2)

instance ExtApplicative (Ph st) st where
    Ph p <* R r = Ph (p . (r .))
    R r *> Ph p = Ph (r . p)
    f <$ R r = Ph (r . ($ f))

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
                                Just (n, t, ss) -> if eqSymTok a t 
                                                    then Step n (push t (k ss))
                                                    else Fail
                                Nothing -> Fail)

instance Eof state => ParserClass Pf state where
    parse (Pf p) st = (fst . eval . p (\st -> if eof st
                                                then undefined 
                                                else error "end")) st

instance Greedy (Pf st) where
    Pf p <<|> Pf q = Pf (\k st -> p k st `best_gr` q k st)

(<++>) :: Pf st [a] -> Pf st [a] -> Pf st [a]
p <++> q = (++) <$> p <*> q

instance Ambiguous (Pf state) where
    amb (Pf p) = Pf (\k inp -> combineValues . removeEndf $ p (\st -> Endf [k st] Fail) inp)

removeEndf :: Steps r -> Steps [r]
removeEndf Fail = Fail
removeEndf (Step n l) = Step n (removeEndf l)
removeEndf (Apply f l) = Apply (map' f) (removeEndf l)
removeEndf (Endf (s:ss) r) = Apply (:(map eval ss)) s `best` removeEndf r

combineValues :: Steps[(a, r)] -> Steps ([a], r)
combineValues lar = Apply (\lar' -> (map fst lar', snd (head lar'))) lar

map' f ~(x:xs) = f x : map f xs

instance Micro (Pf state) where
    micro (Pf p) = Pf (p . (Micro .))

instance Switch Pf where
    switch split (Pf p) = Pf (\k st1 -> let (st2, b) = split st1
                                        in p (\st2' -> k (b st2')) st2)

instance ExtApplicative (Pf st) st where
    Pf p <* R r = Pf (p . r)
    R r *> Pf p = Pf (r . p)
    f <$ R r = Pf (((push f) .) . r)

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

instance Ambiguous (Pm st) where
    amb (Pm ph pf) = Pm (amb ph) (amb pf) 

instance Micro (Pm state) where
    micro (Pm ph pf) = Pm (micro ph) (micro pf)

instance Switch Pm where
    switch split (Pm p q) = Pm (switch split p) (switch split q)

instance ExtApplicative (Pm st) st where
    (Pm ph pf) <* r = Pm (ph <* r) (pf <* r)
    r *> (Pm ph pf) = Pm (r *> ph) (r *> pf)
    f <$ r = Pm (f <$ r) (f <$ r)

-- Parser definition --

-- newtype Parser s t = Parser ([s] -> Maybe (t, [s]))

--     -- Instances --

-- instance Applicative (Parser s) where
--     -- (<*>) :: Parser s (a -> b) -> Parser s a -> Parser s b
--     p1 <*> p2 = [fr r2 | fr <- p1, r2 <- p2]

--     -- (<.) :: Parser s a -> Parser s b -> Parser s a
--     -- p1 <. p2 = const <$> p1 <*> p2

--     -- (.>) :: Parser s a -> Parser s b -> Parser s b
--     -- p1 .> p2 = id <$ p1 <*> p2 
    
--     pure = return

-- instance Functor (Parser s) where
--     -- (<$>) :: (a -> b) -> Parser s a -> Parser s b
--     f `fmap` p = return f <*> p
    
--     -- (<$) :: (b -> c) -> Parser s a -> Parser s (b -> c)
--     -- f <$ p = const <$> return f <*> p

-- instance Monad (Parser s) where
--     -- return :: a -> Parser s a
--     return r = Parser (\inp -> return (r, inp))
    
--     (Parser p) >>= f = Parser (\inp -> [(r', out') | (r, out) <- p inp,
--                                                      let (Parser p') = f r,
--                                                      (r', out') <- p' out])           

-- instance Alternative (Parser s) where
--     -- (<|>) :: Parser s a -> Parser s a -> Parser s a 
--     (Parser p1) <|> (Parser p2) = Parser (\s -> (p1 s) <|> (p2 s))
    
--     -- empty :: Parser s a 
--     empty = Parser (\s -> empty) 

--     -- Run helper --

-- run :: Parser Char a -> String -> Maybe (a, String)
-- run (Parser p) str = p (f str) where 
--     f (x:xs) = if isSpace x then f xs else x : (f xs)
--     f [] = empty 

-- Basic parsers --

token :: (Describes b a, Provides st b a) => [b] -> Pm st [a]
token (x:xs) = sym x <:*> token xs
token [] = return []

r_token :: (Describes b a, Provides st b a) => [b] -> R st [a]
r_token (x:xs) = sym x <:*> r_token xs
r_token [] = return []

-- Pm combinators --
    
    -- Sequencing --

(<**>) :: Pm s a -> Pm s (a -> b) -> Pm s b
p1 <**> p2 = (\a f -> f a) <$> p1 <*> p2

(<:*>) :: (Applicative (p s), Functor (p s)) => p s a -> p s [a] -> p s [a]
p <:*> ps = (:) <$> p <*> ps

(<??>) :: Pm s a -> Pm s (a -> a) -> Pm s a
p1 <??> p2 = p1 <**> (p2 `opt` id)

    -- Choice / Branching --

opt :: Pm s a -> a -> Pm s a
p `opt` v = p <<|> return v

--     -- Iteration --

many :: Pm s a -> Pm s [a]
many p = p <:*> many p `opt` []

many1 :: Pm s a -> Pm s [a]
many1 p = p <:*> many p

chainl :: Pm s (a -> a -> a) -> Pm s a -> Pm s a
chainl op p = applyAll <$> p <*> many (flip <$> op <*> p) 

chainr :: Pm s (a -> a -> a) -> Pm s a -> Pm s a
chainr op p = r where r = p <??> (flip <$> op <*> r)

choice :: [Pm s a] -> Pm s a
choice = foldr (<|>) empty

seqnc :: [Pm s a] -> Pm s [a]
seqnc (p:ps) = p <:*> seqnc ps
seqnc [] = return []

    -- Packing --

pack :: (Describes b a0, Provides st b a0, Describes b a) => [b] -> Pm st a -> [b] -> Pm st a
pack open p close = pack' (r_token open) p (r_token close)

pack' :: R st b -> Pm st a -> R st b -> Pm st a
pack' open p close = open *> p <* close

parens :: (Describes Char a, Provides st Char a) => Pm st a -> Pm st a
parens p = pack "(" p ")"

brackets :: (Describes Char a, Provides st Char a) => Pm st a -> Pm st a
brackets p = pack "[" p "]"

curly :: (Describes Char a, Provides st Char a) => Pm st a -> Pm st a
curly p = pack "{" p "}"

tagged :: (Describes Char a, Provides st Char a) => Pm st a -> Pm st a
tagged p = pack "<" p ">"

-- String Pms --

letter :: (Describes Char a, Provides st Char a) => Pm st a
letter = choice (map sym "abcdefghijklmnopqrstuvwxyz")

word :: (Describes Char a, Provides st Char a) => Pm st [a]
word = many1 letter

-- Number --

digit :: (Describes Char a, Provides st Char a) => Pm st a
digit = choice (map sym "0123456789")

num :: (Provides st Char Int) => Pm st Int
num = (\x -> x) <$> digit

natural :: (Provides st Char Int) => Pm st Int
natural = (foldl (\a b -> a * 10 + b) 0) <$> many1 num

integer :: (Provides st Char Int) => Pm st Int
integer = integer' (r_token "-") 

integer' :: (Provides st Char Int) => R st a -> Pm st Int
integer' negTok = (negate <$ negTok `opt` id) <*> natural

op :: (Describes s a0, Provides st s a0) => (a -> b -> c, [s]) -> Pm st (a -> b -> c)
op (semantic, s) = op' semantic (r_token s)

op' :: (a -> b -> c) -> R st d -> Pm st (a -> b -> c)
op' semantic op_reader = semantic <$ op_reader

anyOp :: (Describes s a0, Provides st s a0) => [(a -> b -> c, [s])] -> Pm st (a -> b -> c)
anyOp = choice . (map op)

addSubtrOps :: (Describes Char a0, Provides st Char a0) => Pm st (Int -> Int -> Int)
addSubtrOps = anyOp [((+), "+"), ((-), "-")]

multDivOps :: (Describes Char a0, Provides st Char a0) => Pm st (Int -> Int -> Int)
multDivOps = anyOp [((*), "*")]

numFactor :: (Provides st Char Int) => Pm st Int
numFactor = integer <|> (parens numExpr)

numExpr :: (Provides st Char Int) => Pm st Int
numExpr = foldr chainl numFactor [addSubtrOps, multDivOps]

expr :: (Provides st Char Int) => Pm st Int
expr = numExpr <|> numIfElse

-- Conditionals --

numIfElse :: (Describes Char a0, Provides st Char a0, Provides st Char Int) => Pm st Int
numIfElse = numIfElse' (r_token "if") (r_token "else")

numIfElse' :: (Provides st Char Int) => R st a -> R st b -> Pm st Int
numIfElse' if_r else_r = (\bool a b -> if toBool bool then a else b) <$ 
       if_r <*> parens numBoolExpr <*> 
            expr <* 
       else_r <*> 
            expr   

numAndOps :: (Describes Char a0, Provides st Char a0) => Pm st (Int -> Int -> Int)
numAndOps = anyOp (map (min,) ["&&", "and"])

numOrOps :: (Describes Char a0, Provides st Char a0) => Pm st (Int -> Int -> Int)
numOrOps = anyOp (map (max,) ["||", "or"])

numBoolExpr :: (Provides st Char Int) => Pm st Int
numBoolExpr = foldr chainl numRelExpr [numAndOps, numOrOps]

numRelOps :: (Describes Char a0, Provides st Char a0) => Pm st (Int -> Int -> Int) 
numRelOps = anyOp [((toInt .) . (<=), "<="), ((toInt .) . (>=), ">="),
                   ((toInt .) . (<), "<"), ((toInt .) . (>), ">")]
-- TODO : Add others

toInt :: Bool -> Int
toInt True = 1
toInt False = 0

toBool :: Int -> Bool
toBool 1 = True
toBool 0 = False

numRelExpr :: (Provides st Char Int) => Pm st Int
numRelExpr = 
    const (toInt False) <$> token "false" <|>
    const (toInt True) <$> token "true" <|>
    expr <**> numRelOps <*> expr 

-- Utils --

applyAll :: a -> [a -> a] -> a
applyAll x (yf:yfs) = applyAll (yf x) yfs
applyAll x [] = x

-- -- Testing --

-- data Token = Identifier -- terminal symbol used in parser
--            | Ident String -- token constructed by scanner
--            | Number Int
--            | If_Symbol
--            | Then_Symbol



-- instance Eq Token where
--     (Ident _) == Identifier = True

-- ident = sym Identifier

-- doubleA :: Pm Char String
-- doubleA = (\c1 c2 -> [c1, c2]) <$> sym 'a' <*> sym 'a'

-- parensH :: Pm Char Int
-- parensH = (max .(1+)) <$> parens parensH <*> parensH `opt` 0

--     -- XML --

-- data Xml = Tag XmlIdent [Xml] | Leaf String deriving Show
-- type XmlIdent = String

-- xmlIdent :: Pm Char XmlIdent
-- xmlIdent = word

-- xmlContent :: Pm Char String
-- xmlContent = many1 (letter <|> digit)

-- openTag :: Pm Char XmlIdent
-- openTag = tagged xmlIdent

-- closeTag :: XmlIdent -> Pm Char XmlIdent
-- closeTag t = tagged (sym '/' *> token t)

-- emptyTag :: Pm Char Xml
-- emptyTag = flip Tag [] <$> tagged (xmlIdent <* sym '/')

-- parseXml :: Pm Char Xml
-- parseXml = [Tag t subt | t <- openTag,
--                          subt <- many parseXml,
--                          _ <- closeTag t]
--            <|> emptyTag
--            <|> (Leaf <$> xmlContent)



