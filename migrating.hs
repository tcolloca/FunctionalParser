{-# LANGUAGE RankNTypes 
           , GADTs
           , MultiParamTypeClasses
           , TypeOperators  
           , FunctionalDependencies
           , FlexibleInstances
           , FlexibleContexts     
#-}

-- RankNTypes for forall in data types (Parser definitions)
-- GADTs Defining new type constructors as function types (Steps)
-- MultiParamTypeClasses for classes with multiple parameters
-- TypeOperators to use class names as infix operators (Describes)
-- FunctionalDependencies for functional dependencies (Provides)
-- FlexibleInstances (i.e. Symbol (Pr state) symbol token)
-- FlexibleContexts (Polymorphic constraints. i.e. Describes Char a)

import Control.Applicative hiding ((<**>), many)

infixr  4  <:*>

-- TODO: Infixes

-- %%%%% TYPE SYNONYMS %%%%% --

type Cost     = Int
type Progress = Int
type Strings  = [String]

-- %%%%% STEPS %%%%% --

data Steps a where
    Step    :: Progress  -> Steps a                            -> Steps a
    Fail    :: Strings   -> [Strings -> Maybe (Cost, Steps a)] -> Steps a
    Apply   :: (b -> a)  -> Steps b                            -> Steps a
    Success :: Steps a                                         -> Steps a
    Endh    :: ([a], [a] -> Steps r) -> Steps (a, r)           -> Steps (a, r)
    Endf    :: [Steps a] -> Steps a  -> Steps a
    Micro   :: Steps a                                         -> Steps a

-- %%%%%%%% INTERFACES %%%%%%%% --

--     &&& STATE  RELATED &&&   --

class symbol `Describes` token where
    eqSymTok    :: symbol -> token -> Bool

class Symbol p symbol token where
    sym         :: symbol -> p token

class Provides state symbol token | state symbol -> token where
    splitState  :: symbol -> state -> Maybe (Progress, token, state)

class Eof state where
    eof         :: state  -> Bool

--     &&& PARSER RELATED &&&   --

--     ~~ GREEDY ~~     --

class Greedy p where
    (<<|>) :: p a -> p a -> p a

best_gr :: Steps a -> Steps a -> Steps a
l `best_gr` r = norm l `best_gr'` norm r
                    where  l@(Step _ _) `best_gr'` _ = l
                           l            `best_gr'` r = l `best` r

class Try p where
    (<<<|>) :: p a -> p a -> p a
    try :: p a -> p a

--     ~~ AMBIGUOUS ~~     --

class Ambiguous p where
    amb :: p a -> p [a]

class Micro p where
    micro :: p a -> p a

--      ~~ SWITCH ~~       --

class Switch p where
    switch :: (st1 -> (st2, st2 -> st1)) -> p st2 a -> p st1 a


-- %%%%% PARSER DEFINITIONS %%%%% --

--     &&&   RECOGNISER    &&&    --

newtype Pr st a = Pr (forall r. (st -> Steps r) -> st -> Steps r)

--     &&& HISTORY  PARSER &&&    --

newtype Ph st a = Ph (forall r. (a -> st -> Steps r) -> st -> Steps r)

--     &&&  FUTURE PARSER  &&&    --

newtype Pf st a = Pf (forall r. (st -> Steps r) -> st -> Steps (a, r))

--     &&& COMBINED PARSER &&&    --

data    Pm st a = Pm (Pr st a) (Ph st a) (Pf st a)

unPr :: Pr st a -> (forall r. (st -> Steps r) -> st -> Steps r)
unPr (Pr r) = r

unPh :: Ph st a-> (forall r. (a -> st -> Steps r) -> st -> Steps r)
unPh (Ph p) = p

unPf :: Pf st a -> (forall r. (st -> Steps r) -> st -> Steps (a, r))
unPf (Pf p) = p

unPm_r :: Pm st a -> (forall r. (st -> Steps r) -> st -> Steps r)
unPm_r (Pm (Pr r) _ _) = r

unPm_h :: Pm st a -> (forall r. (a -> st -> Steps r) -> st -> Steps r)
unPm_h (Pm _ (Ph h) _) = h

unPm_f :: Pm st a -> (forall r. (st -> Steps r) -> st -> Steps (a, r))
unPm_f (Pm _ _ (Pf f)) = f

-- %%%%%% FUNCTOR (Applying a function) %%%%% --

instance Functor (Pr st) where
    --(<$>) :: (b -> a) -> Pr st b -> Pr st a
    f `fmap` (Pr r) = (Pr r)
    --(<$) :: (b -> a) -> Pr st b -> Pr st (b -> a)
    f <$ (Pr r)     = Pr r

instance Functor (Ph st) where
    --(<$>) :: (b -> a) -> Ph st b -> Ph st a
    f `fmap` (Ph p) = Ph (\ k -> p (\ a -> k (f a)))

instance Functor (Pf st) where
    --(<$>) :: (b -> a) -> Pf st b -> Pf st a
    f `fmap` p = pure f <*> p

instance Functor (Pm st) where
    --(<$>) :: (b -> a) -> Pm st b -> Pm st a
    f `fmap` (Pm pr ph pf) = Pm (f `fmap` pr) (f `fmap` ph) (f `fmap` pf)
    --(<$) :: (b -> a) -> Pm st b -> Pm st (b -> a)
    f <$ (Pm (Pr pr) _ _)  = Pm (Pr pr)
                                (Ph (pr . ($ f))) 
                                (Pf (((push f) .) . pr))

-- %%%%% APPLICATIVE (Sequencing) %%%%% --

instance Applicative (Pr st) where
    -- Pr st (a -> b) -> Pr st a -> Pr st b 
    (Pr r1) <*> (Pr r2) = Pr (\ k st -> r1 (r2 k) st)
    -- (<*) :: Pr st a -> Pr st b -> Pr st a
    (Pr r1) <* (Pr r2)  = Pr (r1 . r2)
    -- (*>) :: Pr st a -> Pr st b -> Pr st b
    (Pr r1) *> (Pr r2)  = Pr (r1 . r2)
    -- pure :: a -> Pr st a
    pure r              = Pr (\k st -> k st)

instance Applicative (Ph st) where
    -- (<*>) :: Ph st (a -> b) -> Ph st a -> Ph st b
    (Ph p) <*> (Ph q) = Ph (\ k -> p (\ f -> q (\ a -> k (f a))))
    -- pure :: a -> Ph st a
    pure r            = Ph (\k -> k r)

instance Applicative (Pf st) where
    -- (<*>) :: Pf st (a -> b) -> Pf st a -> Pf st b
    (Pf p) <*> (Pf q) = Pf (\ k st -> applyf (p (q k) st))
    -- pure :: a -> Pf st a
    pure a            = Pf (\k st -> push a (k st))

instance Applicative (Pm st) where
    -- (<*>) :: Pm st (a -> b) -> Pm st a -> Pm st b
    (Pm pr ph pf) <*> ~(Pm qr qh qf)                   = Pm (pr <*> qr) (ph <*> qh) (pf <*> qf)
    -- (<*) :: Pm st a -> Pm st b -> Pm st a
    (Pm (Pr pr) (Ph ph) (Pf pf)) <* ~(Pm (Pr qr) _ _)  = Pm (Pr (pr . qr)) 
                                                            (Ph (ph . (qr .))) 
                                                            (Pf (pf . qr))
    -- (*>) :: Pm st a -> Pm st b -> Pm st b
    (Pm (Pr pr) _ _) *> ~(Pm (Pr qr) (Ph qh) (Pf qf))  = Pm (Pr (pr . qr)) 
                                                            (Ph (pr . qh)) 
                                                            (Pf (pr . qf))
    -- pure :: a -> Pm st a
    pure a                                             = Pm (pure a) (pure a) (pure a)

-- %%%%% ALTERNATIVE (Branching) %%%%% --

instance Alternative (Pr st) where
    --(<|>) :: Pr st a -> Pr st b -> Pr st a
    (Pr r1) <|> (Pr r2) = Pr (\ k inp -> r1 k inp `best` r2 k inp)    
    -- empty :: Pr st a
    empty               = Pr (\ k st -> noAlts)

instance Alternative (Ph st) where
    --(<|>) :: Ph st a -> Ph st b -> Ph st a
    (Ph p1) <|> (Ph p2) = Ph (\ k inp -> p1 k inp `best` p2 k inp)    
    -- empty :: Ph st a
    empty               = Ph (\ k st -> noAlts)

instance Alternative (Pf st) where
    --(<|>) :: Pf st a -> Pf st b -> Pf st a
    (Pf p1) <|> (Pf p2) = Pf (\ k st -> p1 k st `best` p2 k st)
    -- empty :: Pf st a
    empty               = Pf (\ k st -> noAlts)

instance Alternative (Pm st) where
    --(<|>) :: Pm st a -> Pm st b -> Pm st a
    (Pm pr ph pf) <|> (Pm qr qh qf) = Pm (pr <|> qr) (ph <|> qh) (pf <|> qf)
    -- empty :: Pm st a
    empty                           = Pm empty empty empty

-- %%%%% MONAD (Adding effects) %%%%% --

instance Monad (Ph st) where
    -- Ph st a -> (a -> Ph st b) -> Ph st b
    (Ph p) >>= a2q = Ph (\ k -> p (\ a -> unPh (a2q a) k))       

instance Monad (Pm st) where
    -- Pm st a -> (a -> Pm st b) -> Pm st b
    (Pm _ (Ph p) _) >>= a2q = Pm (Pr (\ k -> p (\ a -> unPm_r (a2q a) k)))
                                 (Ph (\ k -> p (\ a -> unPm_h (a2q a) k)))
                                 (Pf (\ k -> p (\ a -> unPm_f (a2q a) k)))

-- %%%%% HELPER FUNCTIONS %%%%%% --

push :: v -> Steps r -> Steps (v, r)
push v = Apply (\s -> (v, s))

applyf :: Steps (b -> a, (b, r)) -> Steps (a, r)
applyf = Apply (\(b2a, ~(b, r)) -> (b2a b, r))

noAlts :: Steps a
noAlts = Fail [] []

applyFail :: (Steps a -> Steps b) -> [(Strings -> Maybe (Cost, Steps a))] -> [(Strings -> Maybe (Cost, Steps b))]
applyFail f = map (\l -> \ strs -> (\ (c, step) -> (c, f step)) <$> l strs)

-- %%%%% BEST %%%%% --

best :: Steps a -> Steps a -> Steps a
l `best` r            = norm l `best'` norm r

best' :: Steps a -> Steps a -> Steps a
Fail sl ll        `best'` Fail sr lr     = Fail (sl ++ sr) (ll ++ lr)
Fail _  _         `best'` r              = r
l                 `best'` Fail  _ _      = l
Step n  l         `best'` Step  m r 
    | n == m                             = Step n (l `best'` r)
    | n <  m                             = Step n (l `best'` Step (m - n) r)
    | n >  m                             = Step m (Step (n - m) l `best'` r)
Micro l           `best'` Micro r        = Micro (l `best` r)
Micro _           `best'`            r   = r
l                 `best'` Micro _        = l
Endf as l         `best'` Endf bs r      = Endf (as ++ bs) (l `best` r)
Endf as l         `best'` r              = Endf as         (l `best` r)
l                 `best'` Endf bs r      = Endf bs         (l `best` r)
Endh (as, k_st) l `best'` Endh (bs, _) r = Endh (as ++ bs, k_st) (l `best` r)
Endh as         l `best'` r              = Endh as               (l `best` r)
l                 `best'` Endh bs      r = Endh bs               (l `best` r)
l                 `best'`  r             = l `best` r 

norm :: Steps a -> Steps a 
norm (Apply f (Step    n l   ) ) = Step n (Apply f l)
norm (Apply f (Fail    ss ls ) ) = Fail ss (applyFail (Apply f) ls)
norm (Apply f (Apply   g l   ) ) = norm (Apply (f . g) l)
norm (Apply f (Success l     ) ) = Success (Apply f l)
norm (Apply f (Micro   l     ) ) = Micro (Apply f l)
norm (Apply f (Endf    as l  ) ) = Endf (map (Apply f) as) (Apply f l)
norm (Apply f (Endh    _  _  ) ) = error "Found Endh on the loose when calling norm!"
norm steps = steps

-- %%%%% SYMBOL %%%%% --

instance (Show symbol, (symbol `Describes` token), (Provides state symbol token))
    => Symbol (Pr state) symbol token where
    -- sym :: symbol -> (Pr state) token 
    sym a = Pr (\ k st -> case splitState a st of
                              Just (n, t, ss) -> if a `eqSymTok` t
                                                     then Step n (k ss)
                                                     else Fail [show a] []
                              Nothing -> Fail [show a] [])

instance (Show symbol, (symbol `Describes` token), (Provides state symbol token))
    => Symbol (Ph state) symbol token where
    -- sym :: symbol -> (Ph state) token 
    sym a = Ph (\ k st -> case splitState a st of
                              Just (n, t, ss) -> if eqSymTok a t 
                                                     then Step n (k t ss)
                                                     else Fail [show a] []
                              Nothing -> Fail [show a] [])

instance (Show symbol, (symbol `Describes` token), (Provides state symbol token))
    => Symbol (Pf state) symbol token where
    -- sym :: symbol -> (Pf state) token 
    sym a = Pf (\ k st -> case splitState a st of
                              Just (n, t, ss) -> if a `eqSymTok` t 
                                                     then Step n (push t (k ss))
                                                     else Fail [show a] []
                              Nothing -> Fail [show a] [])

instance (Show symbol, (symbol `Describes` token), (Provides state symbol token))
    => Symbol (Pm state) symbol token where
    -- sym :: symbol -> (Pm state) token 
    sym a = Pm (sym a) (sym a) (sym a)

-- %%%%% PARSE %%%%% --

parse :: Eof st => Pm st a -> st -> a
parse (Pm _ _ (Pf pf)) = fst . eval . pf (\ rest -> if eof rest
                                                        then undefined
                                                        else error "End exception")

eval :: Steps a -> a
eval (Step    _  l ) = eval l
eval (Fail    ss l ) = error (concat ss)
eval (Apply   f  v ) = f (eval v)
eval (Micro   l    ) = eval l
eval (Success l    ) = eval l
eval (Endh    _  _ ) = error "Found Enh on the loose when calling eval!"
eval (Endf    _  _ ) = error "Found Enf on the loose when calling eval!"

-- %%%%%  GREEDY (Choose left option if it's first symbol gets parsed) %%%%% --

instance Greedy (Pr st) where
    -- (<<|>) :: Pr st a -> Pr st a -> Pr st a
    Pr p <<|> Pr q = Pr (\ k st -> p k st `best_gr` q k st)

instance Greedy (Ph st) where
    -- (<<|>) :: Ph st a -> Ph st a -> Ph st a
    Ph p <<|> Ph q = Ph (\ k st -> p k st `best_gr` q k st)

instance Greedy (Pf st) where
    -- (<<|>) :: Pf st a -> Pf st a -> Pf st a
    Pf p <<|> Pf q = Pf (\ k st -> p k st `best_gr` q k st)

instance Greedy (Pm st) where
    -- (<<|>) :: Pm st a -> Pm st a -> Pm st a
    (Pm pr ph pf) <<|> (Pm qr qh qf) = Pm (pr <<|> qr) (ph <<|> qh) (pf <<|> qf)

--      &&&&  TRY (Greedier!)  &&&&      --

instance Try (Pr st) where
    -- (<<<|>) :: Pr st a -> Pr st a -> Pr st a
    Pr p <<<|> Pr q = Pr (\ k st -> let l = p k st
                                    in maybe (l `best` q k st) id (hasSuccess id l))
    -- try :: Pr st a -> Pr st a
    try (Pr p)      = Pr (p . (Success .))

instance Try (Ph st) where
    -- (<<<|>) :: Ph st a -> Ph st a -> Ph st a
    Ph p <<<|> Ph q = Ph (\ k st -> let l = p k st
                                    in maybe (l `best` q k st) id (hasSuccess id l))
    -- try :: Ph st a -> Ph st a
    try (Ph p)      = Ph (p . (((Success .) .)))

instance Try (Pf st) where
    -- (<<<|>) :: Pf st a -> Pf st a -> Pf st a
    Pf p <<<|> Pf q = Pf (\ k st -> let l = p k st
                                    in maybe (l `best` q k st) id (hasSuccess id l))
    -- try :: Pf st a -> Pf st a
    try (Pf p)      = Pf (p . (Success .))

instance Try (Pm st) where
    -- (<<<|>) :: Pm st a -> Pm st a -> Pm st a
    Pm pr ph pf <<<|> Pm qr qh qf = Pm (pr <<<|> qr) (ph <<<|> qh) (pf <<<|> qf)
    -- try :: Pm st a -> Pm st a
    try (Pm pr ph pf)             = Pm (try pr) (try ph) (try pf)

hasSuccess :: (Steps a -> b) -> Steps a -> Maybe b
hasSuccess f (Step    n l ) = hasSuccess (f . Step n) l
hasSuccess f (Apply   g l ) = hasSuccess (f . (Apply g)) l
hasSuccess f (Success l   ) = Just (f l)
hasSuccess f (Fail    _ _ ) = Nothing

-- %%%%% AMBIGUOUS %%%%% --

instance Ambiguous (Pr st) where
    -- amb :: Pr st a -> Pr st [a]
    amb (Pr pr) = Pr (\ k -> removeEndh . pr (\ st' -> Endh ([undefined], \ _ -> k st') noAlts))

instance Ambiguous (Ph st) where
    -- amb :: Ph st a -> Ph st [a]
    amb (Ph p) = Ph (\ k -> removeEndh . p (\ a st' -> Endh ([a], \ as -> k as st') noAlts))

instance Ambiguous (Pf st) where
    -- amb :: Pf st a -> Pf st [a]
    amb (Pf p) = Pf (\ k inp -> combineValues . removeEndf $ p (\ st -> Endf [k st] noAlts) inp)

instance Ambiguous (Pm st) where
    -- amb :: Pm st a -> Pm st [a]
    amb (Pm pr ph pf) = Pm (amb pr) (amb ph) (amb pf) 

removeEndh :: Steps (a, r) -> Steps r
removeEndh (Step  n          l  ) = Step n (removeEndh l)
removeEndh (Fail  m          ls ) = Fail m (applyFail removeEndh ls)
removeEndh (Apply f          l  ) = error "no apply in history"
removeEndh (Endh  (as, k_st) r  ) = k_st as `best` removeEndh r

removeEndf :: Steps r -> Steps [r]
removeEndf (Step  n      l )  = Step n (removeEndf l)
removeEndf (Fail  m      ls ) = Fail m (applyFail removeEndf ls)
removeEndf (Apply f      l )  = Apply (map' f) (removeEndf l)
removeEndf (Endf  (s:ss) r )  = Apply (:(map eval ss)) s `best` removeEndf r

combineValues :: Steps[(a, r)] -> Steps ([a], r)
combineValues lar = Apply (\lar' -> (map fst lar', snd (head lar'))) lar

map' :: (a -> b) -> [a] -> [b]
map' f ~(x:xs) = f x : map f xs

-- &&&& MICRO (Give lower priority to parser. Only works for lside? Not recommended) &&&& --

instance Micro (Pr st) where
    -- micro :: Pr st a -> Pr st a
    micro (Pr p) = Pr (p . (Micro .))

instance Micro (Ph st) where
    -- micro :: Ph st a -> Ph st a
    micro (Ph p) = Ph (p . (((Micro .) .)))

instance Micro (Pf st) where
    -- micro :: Pf st a -> Pf st a
    micro (Pf p) = Pf (p . (Micro .))

instance Micro (Pm st) where
    -- micro :: Pm st a -> Pm st a
    micro (Pm pr ph pf) = Pm (micro pr) (micro ph) (micro pf)

-- &&&& SWITCH &&&& --

instance Switch Pr where
    -- switch :: (st1 -> (st2, st2 -> st1)) -> Pr st2 a -> Pr st1 a
    switch split (Pr p) = Pr (\ k st1 -> let (st2, b) = split st1
                                         in p (\ st2' -> k (b st2')) st2)

instance Switch Ph where
    -- switch :: (st1 -> (st2, st2 -> st1)) -> Ph st2 a -> Ph st1 a
    switch split (Ph p) = Ph (\ k st1 -> let (st2, st2tost1) = split st1
                                         in p (\ a st2' -> k a (st2tost1 st2')) st2)

instance Switch Pf where
    -- switch :: (st1 -> (st2, st2 -> st1)) -> Pf st2 a -> Pf st1 a
    switch split (Pf p) = Pf (\ k st1 -> let (st2, b) = split st1
                                         in p (\ st2' -> k (b st2')) st2)

instance Switch Pm where
    -- switch :: (st1 -> (st2, st2 -> st1)) -> Pm st2 a -> Pm st1 a
    switch split (Pm pr ph pf) = Pm (switch split pr) (switch split ph) (switch split pf)

--- TEST ---

data Str t = Str {input :: [t],
                  msgs :: [Error t t Int],
                  pos :: !Int,
                  deleteOk :: !Bool } 

listToStr :: String -> Str Char
listToStr ls = Str ls [] 0 True  

instance  Eq a => Describes a a where
    eqSymTok = (==)

data Error t s pos = Inserted s pos String
                    | Deleted t pos String
                    | DeletedAtEnd t
        deriving Show

instance Provides (Str a) a a where
    splitState _ (Str [] _ _ _) = Nothing
    splitState _ (Str (t:ts) msgs pos ok) = Just (pos + 1, t, Str ts msgs (pos + 1) True)

-- instance Provides Str  String Char where
--     splitState "" _ = Nothing
--     splitState _ (Str [] _) = Nothing
--     splitState _ (Str (t:ts) pos) = Just (pos + 1, t, Str ts (pos + 1))    

instance Eof (Str a) where
    eof (Str l _ _ _) = null l
    deleteAtEnd (Str (x:xs) msgs pos ok) = Just (5, Str xs (msgs ++ [DeletedAtEnd x]) pos ok)
    deleteAtEnd _ = Nothing 

instance Stores (Str a) [Error a a Int] where
    getErrors (Str inp msgs pos ok) = (msgs, Str inp [] pos ok)

syma = (sym 'a') :: (Pm (Str Char) Char)

symas = ((\a -> [a]) <$> syma) :: (Pm (Str Char) String)

symb = (sym 'b') :: (Pm (Str Char) Char)

symbs = ((\a -> [a]) <$> symb) :: (Pm (Str Char) String)

tom' = ((\a b -> [a, b]) <$> (sym 'a' <|> sym 'c') <*> sym 'b') :: (Pm (Str Char) [Char])

empty' = empty :: Pm (Str Char) Char

tom'' = ((foldr (:) []) <$> many (sym 'a')) :: (Pm (Str Char) String)




-- Basic parsers --

token :: (Show b, Describes b a, Provides st b a) => [b] -> Pm st [a]
token (x:xs) = sym x <:*> token xs
token [] = return []

r_token :: (Show b, Describes b a, Provides st b a) => [b] -> Pm st [a]
r_token (x:xs) = sym x <:*> r_token xs
r_token [] = return []