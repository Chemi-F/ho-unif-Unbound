module Alpabetic where

import Control.Monad (foldM)

import Data.Char (isDigit, isLetter)
import Text.Parsec
import Text.Parsec.String (Parser)

import Debug.Trace


-- IDentifier
type ID = String

data Term = V ID -- free variable
          | B ID -- bound variable
          | C ID -- constant
          | App Term [Term] -- application
          | Abs ID Term -- abstraction
    deriving (Show, Eq)

type Theta = [(ID, Term)]


-- Nipkow's algorithm
-- (*** Basic Library ***)

subset :: Eq a => [a] -> [a] -> Bool
(x:xs) `subset` ys = (elem x ys) && (xs `subset` ys)
[]     `subset` ys = True

-- intersection
cap :: Eq a => [a] -> [a] -> [a]
(x:xs) `cap` ys = if elem x ys then x:(xs `cap` ys)
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

term2ID :: Term -> ID
term2ID (B s) = s

strip :: Term -> (Term, [Term])
strip (App t ts) = (t, ts)
strip t = (t, [])

-- make Lxs. t
makeAbs :: [Term] -> Term -> Term
makeAbs xs t = foldr (\x t -> Abs x t) t (map term2ID xs)

-- make Lxs. _F@ts
hnf :: [Term] -> Term -> [Term] -> Term
hnf xs _F [] = makeAbs xs _F
hnf xs _F ts = makeAbs xs (App _F ts)


-- (*** Substitutions ***)

-- occur check
occ :: ID -> Theta -> Term -> Bool
occ _F th t = occ' t
    where
        occ' (V _G)    = _F == _G || case lookup _G th of
                                         Just s  -> occ' s
                                         Nothing -> False
        occ' (App t ts) = occ' t || or (map occ' ts)
        occ' (Abs _ s) = occ' s
        occ' _         = False

-- subst x y t = t[x:=y]
subst :: ID -> ID -> Term -> Term
subst x y t = sub t
    where 
        sub (B z)       = if z == x then B y else B z
        sub (App s ss)  = App (sub s) (map sub ss)
        sub (Abs z s)   = if z == x then Abs z s else
                          if z /= y then Abs z (sub s) else
                          let z' = newB
                          in Abs z' $ sub (subst z z' s)
        sub s           = s

-- beta-reduction
red :: Term -> [Term] -> Term
red (Abs x s) (y:ys) = red (subst x (term2ID y) s) ys
red s ys             = App s ys

-- "lazy" form of substitution application
devar :: Theta -> Term -> Term
devar th t =
    case strip t of
        (V _F, ys) ->
            case lookup _F th of
                Just t  -> devar th (red t ys)
                Nothing -> t
        _ -> t


-- (*** Unification ***)

-- projection
proj :: [ID] -> Theta -> Term -> Either String Theta
proj _W th s =
    trace ("proj [" ++ prIDs _W ++ "] " ++ prTheta th ++ " " ++ prTerm s) $

    case strip (devar th s) of
        (Abs x t, _) -> proj (x:_W) th t
        (C _, sm)    -> foldM (proj _W) th sm
        (B x, sm)    -> if elem x _W then foldM (proj _W) th sm
                        else Left "proj fail"
        (V _F, ym)   ->
            if (map term2ID ym) `subset` _W then return th
            else
                let _H = newV
                    zn = ym `cap` (map B _W)
                in return $ (_F, (hnf ym _H zn)) : th

eqs :: Eq a => [a] -> [a] -> Maybe [a]
eqs (x:xs) (y:ys) =
    if x == y then (:) <$> return x <*> eqs xs ys
    else eqs xs ys
eqs [] [] = return []
eqs _  _  = Nothing

flexflex1 :: ID -> [Term] -> [Term] -> Theta -> Either String Theta
flexflex1 _F xm yn th =
    trace ("(4) flexflex1 (" ++ _F ++ ", [" ++ prTerms xm ++
        "], [" ++ prTerms yn ++ "], " ++ prTheta th ++ ")") $

    if xm == yn then return th
    else
        case eqs xm yn of
            Nothing -> Left "flexflex1 (eqs) fail"
            Just zk -> 
                let _H = newV
                in return $ (_F, (hnf xm _H zk)) : th

flexflex2 :: ID -> [Term] -> ID -> [Term] -> Theta -> Either String Theta
flexflex2 _F xm _G yn th =
    trace ("(5) flexflex2 (" ++ _F ++ ", [" ++ prTerms xm ++ "], " ++
        _G ++ ", [" ++ prTerms yn ++ "], " ++ prTheta th ++ ")") $

    if xm `subset` yn then return ((_G, (hnf yn (V _F) xm)) : th) else
    if yn `subset` xm then return ((_F, (hnf xm (V _G) yn)) : th)
    else 
        let _H = newV
            zk = xm `cap` yn
        in return $ (_F, (hnf xm _H zk)) : (_G, (hnf yn _H zk)) : th

flexflex :: ID -> [Term] -> ID -> [Term] -> Theta -> Either String Theta
flexflex _F xm _G yn th = if _F == _G then flexflex1 _F xm yn th
                          else flexflex2 _F xm _G yn th

flexrigid :: ID -> [Term] -> Term -> Theta -> Either String Theta
flexrigid _F xm t th = 
    trace ("(3) flexrigid (" ++ _F ++ ", [" ++ prTerms xm ++
        "], " ++ prTerm t ++ ", " ++ prTheta th ++ ")") $

    if occ _F th t then Left "flexrigid (occ) fail"
    else 
        let lxt = makeAbs xm t
        in proj (map term2ID xm) ((_F, lxt):th) t

unif :: Term -> Term -> Either String Theta
unif s t = unif' [] (s, t)
    where
        unif' th (s, t) =
            trace ("<[" ++ prTerm s ++ " =? " ++ prTerm t ++
                "], " ++ prTheta th ++ ">") $ 

            case (devar th s, devar th t) of
                (Abs x s', Abs y t') -> 
                    unif' th (s', if x == y then t' else subst y x t')
                (Abs x s', t') -> unif' th (s', addApp t' (B x))
                (s', Abs x t') -> unif' th (addApp s' (B x), t')
                (s', t')       -> cases th (s', t')
                where
                    addApp (App t xs) v = App t (xs ++ [v])
                    addApp t v = App t [v]

        cases th (s, t) = case (strip s, strip t) of
            ((V _F, xm), (V _G, yn)) -> flexflex _F xm _G yn th
            ((V _F, xm), _)          -> flexrigid _F xm t th
            (_, (V _G, yn))          -> flexrigid _G yn s th
            ((a, sm), (b, tn))       -> rigidrigid a sm b tn th

        rigidrigid a sm b tn th =
            if a /= b then Left "rigidrigid fail"
            else
                trace ("(2) rigidrigid (" ++  prTerm a ++ ", [" ++ prTerms sm ++
                    "], " ++ prTerm b ++ ", [" ++ prTerms tn ++ "], " ++
                    prTheta th ++ ")") $

                foldM unif' th (zip sm tn)

-- use parser
unifP :: String -> String -> IO ()
unifP t1 t2 =
    case parser t1 of
        Left e1   -> putStrLn $ show e1
        Right t1' ->
            case parser t2 of
                Left e2   -> putStrLn $ show e2
                Right t2' -> putStrLn $ prUnif t1' t2'


-- Print

prTerm :: Term -> String
prTerm (V x) = x
prTerm (B x) = "#" ++ x
prTerm (C x) = "_" ++ x
prTerm (App t ts) = prTerm t ++ "(" ++ prTerms ts ++ ")"
prTerm (Abs x t) = prAbs [x] t
    where
        prAbs ids (Abs x t) = prAbs (ids ++ [x]) t
        prAbs ids t = "L" ++ prIDs ids ++ "." ++ prTerm t

prIDs :: [ID] -> String
prIDs [] = ""
prIDs (x:[]) = x
prIDs (x:xs) = x ++ "," ++ prIDs xs

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

prUnif :: Term -> Term -> String
prUnif t1 t2 = 
    case unif t1 t2 of
        Left e -> e
        Right th' -> prTheta th'


-- parser

-- BNF
-- expr = 'L' IDs '.' term | term
-- term = factor '(' terms ')'
-- factor = '(' expr ')' | literal
-- literal = var | constant | bound
--
-- IDs = ID ( ',' IDs )*
-- terms = expr ( ',' terms )*

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
term = do
    f <- factor 
    do
        spaces >> char '(' >> spaces
        ts <- pTerms
        spaces >> char ')' >> spaces
        return (App f ts)
        <|> return f

pTerms :: Parser [Term]
pTerms = do
    e <- expr
    do
        spaces >> char ',' >> spaces
        ts <- pTerms
        return (e:ts)
        <|> return [e]

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
