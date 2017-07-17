{-# LANGUAGE FlexibleInstances
           , MultiParamTypeClasses    
#-}

import Parslib.Parsers
import Parslib.Combinators
import Control.Applicative hiding ((<**>), many)
import Data.List (intercalate)

-- %%%% BOT PARSER %%%% --

-- Bot Parser es un parser de la configuración de un bot para canales de IRC donde en 
-- función de lo que los usuarios dicen, el bot responde ciertas cosas.

-- %%%% MOTIVACION %%%% --

-- Previamente la configuración del bot era mediante un JSON, y los usuarios tenían
-- problemas con entender dicho formato, particularmente cuando faltaba una llave ({})
-- u otro símbolo. 

-- %%%% REGLAS DE EJEMPLO %%%% --

-- si \"juan\" dice \"hola\" entonces decir \"hola :)\"
-- si \"juan\" dice \"chau\" y \"pedro\" dice \"chau\" o \"ana\" dice \"adios\" entonces decir \"chau!\"
-- si lo que dice \"juan\" contiene \"bot\" y no empieza con \"hola\" decir \"que pasa?\" sino \"Hey!\"

-- %%%% EXTENSIONES %%%% --

-- Posibles extensiones tendrían como condición si un usuario entra o sale de un canal.

-- Otra extensión sería la posibilidad de convertir la estructura a un JSON y reutilizar
-- el código existente del bot.

-- %%%% EJEMPLO PARA CORRER %%%% --

-- test botParser "{si lo que dice \"juan\" contiene \"bot\" y no empieza con \"hola\" decir \"que pasa?\".}"

-- %%%% CODIGO %%%% --

-- Definición del estado. Se guarda la cadena de símbolos, progreso y posición.

data StrState s = StrState {
                  input :: [s],
                  prog  :: !Int,
                  pos   :: !Position} 

type Position = (Int, Int)

class DescribesPosition a where
    updatePos :: Position -> a -> Position

instance DescribesPosition a => Provides (StrState a) a a Position where
    splitState s (StrState []     _    pos ) = (pos, Nothing)                                
    splitState s (StrState (t:ts) prog pos ) = (pos, Just (prog + 1, t, StrState ts (prog + 1) newpos)) 
                                              where newpos = updatePos pos s

instance DescribesPosition Char where
    updatePos (l, c) '\t' = (l    , c + 4)
    updatePos (l, c) '\n' = (l + 1, 0    )
    updatePos (l, c) _    = (l    , c + 1)

instance Eof (StrState a) where
    eof (StrState l _ _) = null l


stringToStrState :: String -> StrState Char
stringToStrState ls = StrState ls 0 (0, 0) 

test :: Parser (StrState Char) a -> String -> a
test p str = parse p (stringToStrState str)

testFile :: Parser (StrState Char) a -> String -> IO a
testFile p filename = do {
                        contents <- readFile filename;
                        return (parse p (stringToStrState contents))
                      }

main :: IO ()
main = do {
         filename <- readFile "config.properties";
         rules    <- testFile botParser filename;
         writeFile "structure.txt" (show rules)
       }

-- %%%% ESTRUCTURA QUE GENERA EL BOTPARSER %%%% --

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


-- %%%% CONSTRUCCION DEL BOT PARSER %%%% --

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
pUsuario = doubleQuoted ident

optUsuario :: Username -> Parser BotState Username
optUsuario []   = pUsuario
optUsuario prev = (pUsuario <?|> (prev, id))

pMensaje :: Parser BotState String
pMensaje = doubleQuoted string

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
                          (     optUsuario usrAnterior <* pDice 
                            <|> pLoQueDice *> optUsuario usrAnterior <* pEs) 
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

-- propagarUsuario permite que en la siguiente condición no se especifique el usuario, y se use el último especificado.

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
botParser = curly (many1 pSiEntonces)

-- toJson :: [Rule] -> String
-- toJson rs = "{\n" ++ intercalate ", \n" (map (ruleToJson 1) rs) ++ "\n}"

-- ruleToJson :: Int -> Rule -> String
-- ruleToJson n (IfThenElse cond a1 a2) = 
--   tab n       ++ "{\n"                                             ++ 
--   tab (n + 1) ++   "\"condition\":   " ++ (conditionToJson 3 cond) ++
--   tab (n + 1) ++   "\"ifAction\" :   " ++ (actionToJson    3 a1)   ++ 
--   tab (n + 1) ++   "\"ifAction\" :   " ++ (actionToJson    3 a2)   ++
--   tab n       ++ "}\n" 

-- actionToJson :: Int -> Action -> String
-- actionToJson n (Say str) = "\n"                         ++ 
--   tab n       ++ "{\n"                                  ++
--   tab (n + 1) ++   "\"say\": " ++ "\"" ++ str ++ "\"\n" ++
--   tab n       ++ "}\n"
-- actionToJson n None = "null\n"

-- conditionToJson :: Int -> Condition -> String
-- conditionToJson n cond = "None\n"

-- -- {
-- --   "y: " condicion
-- --   "y: " condicion

-- -- }

-- -- {
-- --   {
-- --     "condition":
-- --       {

-- --       }

-- --   }
-- -- }

-- tab :: Int -> String
-- tab n = replicate n '\t'