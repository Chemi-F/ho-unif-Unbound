module Alpabetic where

import Data.Char (isDigit, isLetter)
import Text.Parsec
import Text.Parsec.String (Parser)

import Debug.Trace


-- IDentifier
type ID = String

data Term = V ID -- free variable
          | B ID -- bound variable
          | C ID -- constant
          | App Term Term -- application
          | Abs ID Term -- abstraction
    deriving (Show, Eq)

type Theta = [(ID, Term)]


-- Nipkow's algorithm
-- (*** Basic Library ***)

-- foldl
myfoldl :: ((a, b) -> a) -> (a, [b]) -> a
myfoldl f (a, (x:xs)) = myfoldl f ((f (a, x)), xs)
myfoldl _ (a, [])     = a

-- foldr
myfoldr :: ((a, b) -> b) -> ([a], b) -> b
myfoldr f ((x:xs), a) = f (x, (myfoldr f (xs, a)))
myfoldr _ ([], a)     = a

-- lookup
assoc :: Eq t => t -> [(t, a)] -> Maybe a
assoc x ((y, t):ps) = if x == y then Just t else assoc x ps
assoc _ []          = Nothing

-- elem
mem :: Eq t => t -> [t] -> Bool
x `mem` (y:ys) = x == y || x `mem` ys
x `mem` []     = False

subset :: Eq a => [a] -> [a] -> Bool
(x:xs) `subset` ys = (x `mem` ys) && (xs `subset` ys)
[]     `subset` ys = True

-- intersection
cap :: Eq a => [a] -> [a] -> [a]
(x:xs) `cap` ys = if x `mem` ys then x:(xs `cap` ys)
                  else xs `cap` ys
[]     `cap` _  = []


-- (*** Terms ***)

-- newB, newV : not work
-- create new bound var name
newB :: ID
newB = "NEW BNAME"

-- create new free var name
newV :: Term
newV = V "NEW VNAME"

b1 :: Term -> ID
b1 (B s) = s

-- (...(a.s1)...).sn -> (a, [s1,...,sn])
strip :: Term -> (Term, [Term])
strip t = strip' (t, [])
    where
        strip' (App s t, ts) = strip' (s, t:ts)
        strip' p = p

-- abs
-- make Lxs. t
myabs :: ([Term], Term) -> Term
myabs (xs, t) = myfoldr (\(t, x) -> Abs t x) (map b1 xs, t)

-- make Lxs. _F@ts
hnf :: ([Term], Term, [Term]) -> Term
hnf (xs, _F, ss) = myabs (xs, (myfoldl (\(f, s) -> App f s) (_F, ss)))


-- (*** Substitutions ***)

-- occur check
occ :: ID -> Theta -> Term -> Bool
occ _F _S t = occ' t
    where
        occ' (V _G)    = _F == _G || case assoc _G _S of
                                         Just s  -> occ' s
                                         Nothing -> False
        occ' (App s t) = occ' s || occ' t
        occ' (Abs _ s) = occ' s
        occ' _         = False

-- subst y x t = t[x:=y]
subst :: ID -> ID -> Term -> Term
subst y x t = sub t
    where 
        sub (B z)       = if z == x then B y else B z
        sub (App s1 s2) = App (sub s1) (sub s2)
        sub (Abs z s)   = if z == x then Abs z s else
                          if z /= y then Abs z (sub s) else
                          let z' = newB
                          in Abs z' $ sub (subst z' z s)
        sub s           = s

-- reduction
red :: Term -> [Term] -> Term
red (Abs x s) (y:ys) = red (subst (b1 y) x s) ys
red s (y:ys)         = red (App s y) ys
red s []             = s

-- "lazy" form of substitution application
devar :: Theta -> Term -> Term
devar _S t =
    case strip t of
        ((V _F), ys) ->
            case assoc _F _S of
                Just t  -> devar _S (red t ys)
                Nothing -> t
        _ -> t


-- (*** Unification ***)

-- projection
proj :: [ID] -> (Theta, Term) -> Theta
proj _W (_S, s) =
    case strip (devar _S s) of
        (Abs x t, _) -> proj (x:_W) (_S, t)
        (C _, ss)    -> myfoldl (proj _W) (_S, ss)
        (B x, ss)    -> if x `mem` _W then myfoldl (proj _W) (_S, ss)
                        else trace ("Fail") $ [("", V "")]
        (V _F, ss)   ->
            if (map b1 ss) `subset` _W then _S
            else (_F, hnf (ss, newV, ss `cap` (map B _W))) : _S
    where
        prIDs [] = ""
        prIDs (x:[]) = x
        prIDs (x:xs) = x ++ ", " ++ prIDs xs


eqs :: Eq a => [a] -> [a] -> [a]
eqs (x:xs) (y:ys) =
    if x == y then x:(eqs xs ys)
    else eqs xs ys
eqs [] [] = []
eqs _  _  = trace ("Fail") $ []

flexflex1 :: (ID, [Term], [Term], Theta) -> Theta
flexflex1 (_F, ym, zn, _S) =
    if ym == zn then _S
    else (_F, hnf (ym, newV, (eqs ym zn))) : _S

flexflex2 :: (ID, [Term], ID, [Term], Theta) -> Theta
flexflex2 (_F, ym, _G, zn, _S) =
    if ym `subset` zn then (_G, hnf (zn, V _F, ym)) : _S else
    if zn `subset` ym then (_F, hnf (ym, V _G, zn)) : _S
    else let _H = newV
             xk = ym `cap` zn
         in (_F, hnf (ym, _H, xk)) : (_G, hnf (zn, _H, xk)) : _S

flexflex :: (ID, [Term], ID, [Term], Theta) -> Theta
flexflex (_F, ym, _G, zn, _S) = if _F == _G then flexflex1 (_F, ym, zn, _S)
                                else flexflex2 (_F, ym, _G, zn, _S)

flexrigid :: (ID, [Term], Term, Theta) -> Theta
flexrigid (_F, ym, t, _S) = 
    if occ _F _S t then trace ("Fail") $ [("", V "")]
    else proj (map b1 ym) (((_F, myabs (ym, t)) : _S), t)

unif :: (Theta, (Term, Term)) -> Theta
unif (_S, (s, t)) =
    case (devar _S s, devar _S t) of
        (Abs x s, Abs y t) -> 
            unif (_S, (s, if x == y then t else subst x y t)) 
        (Abs x s, t) -> unif (_S, (s, App t (B x)))
        (s, Abs x t) -> unif (_S, (App s (B x), t))
        (s, t)       -> cases _S (s, t)

    where
        cases _S (s, t) =
            case (strip s, strip t) of
                ((V _F, ym), (V _G, zn)) -> flexflex (_F, ym, _G, zn, _S)
                ((V _F, ym), _)          -> flexrigid (_F, ym, t, _S)
                (_, (V _F, ym))          -> flexrigid (_F, ym, s, _S)
                ((a,sm), (b,tn))         -> rigidrigid (a, sm, b, tn, _S)

        rigidrigid (a, sm, b, tn, _S) =
            if a /= b then trace ("Fail") $ [("", V "")]
            else myfoldl unif (_S, zip sm tn)

-- use parser
unifP :: String -> String -> IO ()
unifP t1 t2 =
    case parser t1 of
        Left e1   -> putStrLn $ show e1
        Right t1' ->
            case parser t2 of
                Left e2   -> putStrLn $ show e2
                Right t2' -> putStrLn $ prTheta $ unif ([], (t1', t2'))


-- Print

prTerm :: Term -> String
prTerm (V x) = x
prTerm (B x) = "#" ++ x
prTerm (C x) = "_" ++ x
prTerm (App t1 t2) =
    let (t, ts) = strip (App t1 t2)
    in prTerm t ++ "(" ++ prTerms ts ++ ")"
prTerm (Abs x t) = prAbs [x] t
    where
        prAbs ids (Abs x t) = prAbs (ids ++ [x]) t
        prAbs ids t = "L" ++ prIDs ids ++ "." ++ prTerm t

prIDs :: [ID] -> String
prIDs [] = ""
prIDs (x:[]) = show x
prIDs (x:xs) = show x ++ "," ++ prIDs xs

prTerms :: [Term] -> String
prTerms [] = ""
prTerms (x:[]) = prTerm x
prTerms (x:xs) = 
    let x'  = prTerm x
        xs' = prTerms xs
    in x' ++ ", " ++ xs'

prTheta :: Theta -> String
prTheta t = "{" ++ prTheta' t
    where
        prTheta' [] = "}"
        prTheta' ((id, t):[]) = id ++ " -> " ++ prTerm t ++ "}"
        prTheta' ((id, t):ss) = id ++ " -> " ++ prTerm t ++ ", " ++ prTheta ss

-- Parser

-- BNF
-- expr = 'L' IDs '.' term | term
-- term = factor ( '@' factor )*
-- factor = '(' expr ')' | literal
-- literal = var | constant | bound
--
-- IDs = ID ( ',' IDs )*

parser :: String -> Either ParseError Term
parser s = parse expr "Term" s

expr :: Parser Term
expr = do
    spaces >> char 'L' >> spaces
    ids <- pIDs
    spaces >> char '.' >> spaces
    t <- term
    return $ foldr (\id t -> Abs id t) t ids
    <|> term

pIDs :: Parser [ID]
pIDs = do
    id <- pString
    do
        spaces >> char ',' >> spaces
        ids <- pIDs
        return (id:ids)
        <|> return [id]

term :: Parser Term
term = chainl1 factor pApp

pApp :: Parser (Term -> Term -> Term)
pApp = do
    spaces >> char '@' >> spaces
    return App

factor :: Parser Term
factor = do
    spaces >> char '(' >> spaces
    e <- expr
    spaces >> char ')' >> spaces
    return e
    <|> literal

literal :: Parser Term
literal = pConstant <|> pBound <|> pVar

pConstant :: Parser Term
pConstant = do
    spaces >> char '_' >> spaces
    id <- pString
    spaces
    return $ C id

pBound :: Parser Term
pBound = do
    spaces >> char '#' >> spaces
    id <- pString
    spaces
    return $ B id

pVar :: Parser Term
pVar = do
    spaces
    id <- pString
    spaces
    return $ V id 
          
pString :: Parser String
pString = do
    fc <- firstChar
    rest <- many nonFirstChar
    return (fc:rest)
    where
        firstChar = satisfy (\a -> isLetter a)
        nonFirstChar = satisfy (\a -> isDigit a || isLetter a)
