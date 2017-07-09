{-# LANGUAGE FlexibleInstances
           , MultiParamTypeClasses    
#-}

import Parslib.Parsers
import Parslib.Combinators
import Control.Applicative hiding ((<**>), many)
import Data.List (intercalate)

--- TEST ---

class DescribesPosition a where
    updatePos :: Position -> a -> Position

data StrState s = StrState {input :: [s],
                  prog  :: !Int,
                  pos   :: !Position} 

type Position = (Int, Int)

instance DescribesPosition a => Provides (StrState a) a a Position where
    splitState s (StrState []     _    pos ) = (pos, Nothing)                                
    splitState s (StrState (t:ts) prog pos ) = (pos, Just (prog + 1, t, StrState ts (prog + 1) newpos)) 
                                              where newpos = updatePos pos s

instance Eof (StrState a) where
    eof (StrState l _ _) = null l

instance DescribesPosition Char where
    updatePos (l, c) '\t' = (l    , c + 4)
    updatePos (l, c) '\n' = (l + 1, 0    )
    updatePos (l, c) _    = (l    , c + 1)

stringToStrState :: String -> StrState Char
stringToStrState ls = StrState ls 0 (0, 0) 

test :: Parser (StrState Char) a -> String -> a
test p str = parse p (stringToStrState str)

testJson :: Parser (StrState Char) [Rule] -> String -> String
testJson p str = toJson (test p str)

syma = (sym 'a') :: (Parser (StrState Char) Char)

symas = ((\a -> [a]) <$> syma) :: (Parser (StrState Char) String)

symb = (sym 'b') :: (Parser (StrState Char) Char)

symbs = ((\a -> [a]) <$> symb) :: (Parser (StrState Char) String)

tom' = ((\a b -> [a, b]) <$> (sym 'a' <|> sym 'c') <*> sym 'b') :: (Parser (StrState Char) [Char])

empty' = empty :: Parser (StrState Char) Char

tom'' = ((foldr (:) []) <$> many (sym 'a')) :: (Parser (StrState Char) String)


data Rule          = IfThenElse Condition Action Action 
    deriving Show

data Action        = Say String 
                   | None 
    deriving Show

data Condition     = Not   Condition 
                   | And   Condition      Condition 
                   | Or    Condition      Condition 
                   | Atom  AtomCondition 
    deriving Show 

data AtomCondition = SaysEq       String Username
                   | SaysContains String Username
                   | SaysStarts   String Username
                   | SaysEnds     String Username
    deriving Show


type BotState = StrState Char
type Username = String

noStr :: String
noStr = "no "

pSi :: Parser BotState String
pSi = token "si "

pEntonces :: Parser BotState String
pEntonces = token "entonces "

pSino :: Parser BotState String
pSino = token "sino "

pNo :: Parser BotState String
pNo = token noStr

pEs :: Parser BotState String
pEs = token "es "

pLo :: Parser BotState String
pLo = token "lo "

pQue :: Parser BotState String
pQue = token "que "

pDice :: Parser BotState String
pDice = token "dice "

pDecir :: Parser BotState String
pDecir = token "decir "

pFin :: Parser BotState String
pFin = token "."

pLoQueDice :: Parser BotState String
pLoQueDice = pLo *> pQue *> pDice

pUsuario :: Parser BotState Username
pUsuario = doubleQuoted word

optUsuario :: Username -> Parser BotState Username
optUsuario []   = pUsuario
optUsuario prev = (pUsuario <?|> (prev, id))

pMensaje :: Parser BotState String
pMensaje = doubleQuoted word

condUniOp :: Parser BotState (Condition -> Condition)
condUniOp = strAnyUniOp [(Not, noStr)]

yOp :: Parser BotState (Condition -> Condition -> Condition)
yOp = strAnyBiOp [(And, "y ")]

oOp :: Parser BotState (Condition -> Condition -> Condition)
oOp = strAnyBiOp [(Or, "o ")]

pCumpleRelacion :: Parser BotState (Username -> String -> AtomCondition)
pCumpleRelacion = strAnyUniOp [(SaysContains, "contiene ")] <|> strAnyUniOp[(SaysStarts, "empieza "), (SaysEnds, "termina ")] <* token "con "

pDiceNoEs :: Username -> Parser BotState (Username, Condition)
pDiceNoEs usrAnterior = toUserPair (((Not . Atom) .) . SaysEq) <$> 
                            (   optUsuario usrAnterior <* pNo <* pDice 
                            <|> pLoQueDice *> optUsuario usrAnterior <* pNo <* pEs) 
                          <*> pMensaje

pDiceEs :: Username -> Parser BotState (Username, Condition)
pDiceEs usrAnterior = toUserPair ((Atom .) . SaysEq) <$> 
                          (optUsuario usrAnterior <* pDice <|> pLoQueDice *> optUsuario usrAnterior <* pEs) 
                          <*> pMensaje

pDiceCondicion :: Username -> Parser BotState (Username, Condition)
pDiceCondicion usrAnterior = (\ x f g y -> toUserPair ((f .) . g) x y) <$> 
                          (pLoQueDice ?*> optUsuario usrAnterior) 
                          <*> (pNo <?|> (Atom, const (Not . Atom))) 
                          <*> pCumpleRelacion 
                          <*> pMensaje

toUserPair :: (Username -> String -> Condition) -> Username -> String -> (Username, Condition)
toUserPair f = \ user msg -> (user, f user msg)

condAtom :: Username -> Parser BotState (Username, Condition)
condAtom usrAnterior = choice (map ($ usrAnterior) [pDiceEs, pDiceNoEs, pDiceCondicion]) 

condicionBool :: Username -> Parser BotState (Username, Condition)
condicionBool = foldr propagarUsuario condAtom [oOp, yOp]

propagarUsuario :: (Alternative p, Monad p) => p (b -> b -> b) -> (a -> p (a, b)) -> a -> p (a, b)
propagarUsuario op pf a = do {
      (a', b')   <- pf a
    ; f          <- op
    ; (a'', b'') <- propagarUsuario op pf a'
    ; return (a'', (f b' b''))} <|> pf a

pCumpleCondicion :: Parser BotState Condition
pCumpleCondicion = snd <$> condicionBool []

pHacerAlgo :: Parser BotState Action
pHacerAlgo = Say <$> (pDecir *> pMensaje)

optDecir :: Parser BotState Action
optDecir = Say <$> (pDecir ?*> pMensaje)

pSinoHacerOtraCosa :: Parser BotState Action
pSinoHacerOtraCosa = ((pSino *> optDecir) <?|> (None, id))

pSiEntonces :: Parser BotState Rule
pSiEntonces = IfThenElse <$> 
             (pSi *> pCumpleCondicion) 
             <*> (pEntonces ?*> pHacerAlgo) 
             <*> pSinoHacerOtraCosa 
             <*  pFin

botParser :: Parser BotState [Rule]
botParser = curly (many pSiEntonces)

toJson :: [Rule] -> String
toJson rs = "{\n" ++ intercalate ", \n" (map (ruleToJson 1) rs) ++ "\n}"

ruleToJson :: Int -> Rule -> String
ruleToJson n (IfThenElse cond a1 a2) = 
  tab n       ++ "{\n"                                             ++ 
  tab (n + 1) ++   "\"condition\":   " ++ (conditionToJson 3 cond) ++
  tab (n + 1) ++   "\"ifAction\" :   " ++ (actionToJson    3 a1)   ++ 
  tab (n + 1) ++   "\"ifAction\" :   " ++ (actionToJson    3 a2)   ++
  tab n       ++ "}\n" 

actionToJson :: Int -> Action -> String
actionToJson n (Say str) = "\n"                         ++ 
  tab n       ++ "{\n"                                  ++
  tab (n + 1) ++   "\"say\": " ++ "\"" ++ str ++ "\"\n" ++
  tab n       ++ "}\n"
actionToJson n None = "null\n"

conditionToJson :: Int -> Condition -> String
conditionToJson n cond = "None\n"

-- {
--   "y: " condicion
--   "y: " condicion

-- }

-- {
--   {
--     "condition":
--       {

--       }

--   }
-- }

tab :: Int -> String
tab n = replicate n '\t'