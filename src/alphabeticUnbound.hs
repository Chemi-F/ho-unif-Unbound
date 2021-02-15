{-# LANGUAGE MultiParamTypeClasses
           , TemplateHaskell
           , ScopedTypeVariables
           , FlexibleInstances
           , FlexibleContexts
           , UndecidableInstances
  #-}

module AlpabeticUnbound where

import Unbound.LocallyNameless

import Control.Monad (foldM)
import Control.Monad.Except
import Control.Monad.Trans.Maybe
import Control.Applicative ((<|>), many)

import Data.Char (isDigit, isLetter)
import Text.Parsec hiding ((<|>), many)
import Text.Parsec.String (Parser)


-- IDentifier
type ID = Name Term
type CID = String

data Term = V ID -- variable
          | F ID -- free variable
          | C CID -- constant
          | App Term [Term] -- application
          | Abs (Bind ID Term) -- abstraction
    deriving Show

-- deriving Eq can't use
instance Eq Term where
    (V x) == (V y) = x == y
    (F x) == (F y) = x == y
    (C x) == (C y) = x == y
    _ == _ = False

type Theta = [(ID, Term)]


-- *** Unbound ***
$(derive [''Term])

instance Alpha Term

instance Subst Term Term where
    isvar (V v) = Just (SubstName v)
    isvar (F v) = Just (SubstName v)
    isvar _     = Nothing

-- c, v, lam :: for parser
c :: String -> Term
c = C

v :: String -> Term
v = V . string2Name

lam :: String -> Term -> Term
lam x t = Abs $ bind (string2Name x) t
-- *** Unbound ***

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

-- create new free var name
-- avoid (F, G) H --> H
-- avoid (F, H) H --> H1
newFv :: LFresh m => [AnyName] -> m Term
newFv anys = F <$> newName anys
    where
        newName anys = avoid anys (lfresh $ string2Name "H")

term2ID :: Term -> ID
term2ID (V id) = id

strip :: Term -> (Term, [Term])
strip (App t ts) = (t, ts)
strip t = (t, [])

-- make Lxs. t
makeAbs :: LFresh m => [Term] -> Term -> m Term
makeAbs xs t = return $ foldr (\x t -> Abs (bind x t)) t (map term2ID xs)

-- make Lxs. _F@ts
hnf :: LFresh m => [Term] -> Term -> [Term] -> m Term
hnf xs _F ts = makeAbs xs (App _F ts)


-- (*** Substitutions ***)

-- occur check
occ :: ID -> Theta -> Term -> Bool
occ _F th t = occ' t
    where
        occ' (F _G)    = _F == _G || case lookup _G th of
                                         Just t  -> occ' t
                                         Nothing -> False
        occ' (App t ts) = occ' t || or (map occ' ts)
        occ' (Abs b)   = let ids = fv (Abs b) :: [ID]
                         in elem _F ids
        occ' _         = False

-- in Unbound.LocallyNameless.Subst
-- subst :: ID -> Term -> Term -> Term
-- subst x y t = t[x:=y]

-- beta-reduction
red :: LFresh m => Term -> [Term] -> m Term
red (Abs b) (y:ys) = lunbind b $ \(x, s) -> red (subst x y s) ys
red s ys           = return $ App s ys

-- "lazy" form of substitution application
devar :: LFresh m => Theta -> Term -> m Term
devar th t =
    case strip t of
        (F _F, ys) ->
            case lookup _F th of
                Just t -> do
                    t' <- red t ys
                    devar th t'
                Nothing -> return $ t
        _ -> return t


-- (*** Unification ***)

-- projection
proj :: [ID] -> Theta -> Term -> ExceptT String (LFreshMT IO) Theta
proj _W th s = do
    prth <- prTheta th
    prs  <- prTerm s
    liftIO $ putStrLn $ "proj [" ++ prIDs _W ++ "] " ++ prth ++ " " ++ prs

    s' <- devar th s
    case strip s' of
        (Abs b, _) -> lunbind b $ \(x, t) -> proj (x:_W) th t
        (C _, sm)  -> foldM (proj _W) th sm
        (V x, sm)  -> if elem x _W then foldM (proj _W) th sm
                      else throwError "proj fail"
        (F _F, ym) ->
            if (map term2ID ym) `subset` _W then return th
            else do 
                let fvs = fvAny (F _F)
                let zn  = ym `cap` (map V _W)
                _H <- newFv fvs
                lH <- hnf ym _H zn
                return $ (_F, lH) : th

eqs :: Eq a => [a] -> [a] -> Maybe [a]
eqs (x:xs) (y:ys) =
    if x == y then (:) <$> return x <*> eqs xs ys
    else eqs xs ys
eqs [] [] = return []
eqs _  _  = Nothing

flexflex1 :: ID -> [Term] -> [Term] -> Theta -> ExceptT String (LFreshMT IO) Theta
flexflex1 _F xm yn th = do
    prxm <- prTerms xm
    pryn <- prTerms yn
    prth <- prTheta th
    liftIO $ putStrLn $ "(4) flexflex1 (" ++ show _F ++
        ", [" ++ prxm ++ "], [" ++ pryn ++ "], " ++ prth ++  ")"

    if xm == yn then return th
    else case eqs xm yn of
        Nothing -> throwError "flexflex1 (eqs) fail"
        Just zk -> do
            let fvs = fvAny (F _F)
            _H <- newFv fvs
            lH <- hnf xm _H zk
            return $ (_F, lH) : th

flexflex2 :: ID -> [Term] -> ID -> [Term] -> Theta -> ExceptT String (LFreshMT IO) Theta
flexflex2 _F xm _G yn th = do
    prxm <- prTerms xm
    pryn <- prTerms yn
    prth <- prTheta th
    liftIO $ putStrLn $ "(5) flexflex2 (" ++ show _F ++ ", [" ++
        prxm ++ "], " ++ show _G ++ ", [" ++ pryn ++ "], " ++ prth ++  ")"

    if xm `subset` yn then do
        lF <- hnf yn (V _F) xm
        return $ (_G, lF) : th
    else if yn `subset` xm then do
        lG <- hnf xm (V _G) yn
        return $ (_F, lG) : th
    else do
        let fvs = fvAny (F _F) ++ fvAny (F _G)
        let zk = xm `cap` yn
        _H  <- newFv fvs
        lxH <- hnf xm _H zk
        lyH <- hnf yn _H zk
        return $ (_F, lxH) : (_G, lyH) : th

flexflex :: ID -> [Term] -> ID -> [Term] -> Theta -> ExceptT String (LFreshMT IO) Theta
flexflex _F xm _G yn th = if _F == _G then flexflex1 _F xm yn th
                          else flexflex2 _F xm _G yn th

flexrigid :: ID -> [Term] -> Term -> Theta -> ExceptT String (LFreshMT IO) Theta
flexrigid _F xm t th = do
    prxm <- prTerms xm
    prt  <- prTerm t
    prth <- prTheta th
    liftIO $ putStrLn $ "(3) flexrigid (" ++ show _F ++
        ", [" ++ prxm ++ "], " ++ prt ++ ", " ++ prth ++  ")"

    if occ _F th t then throwError "flexrigid (occ) fail"
    else do
        lxt <- makeAbs xm t
        proj (map term2ID xm) ((_F, lxt):th) t

-- ExceptT String LFreshM Theta
--   Left (String)
--   Right (LFreshM Theta)
unif :: Term -> Term -> ExceptT String (LFreshMT IO) Theta
unif s t =
    let s' = v2f s
        t' = v2f t
    in unif' [] (s', t')
    where
        v2f t = let fvs = fv t :: [ID]
                in foldl (\t x -> subst x (F x) t) t fvs
        unif' th (s, t) = do
            prth <- prTheta th
            prs  <- prTerm s
            prt  <- prTerm t
            liftIO $ putStrLn $ "<[" ++ prs ++ " =? " ++ prt ++ "], " ++ prth ++ ">"

            ds <- devar th s
            dt <- devar th t
            case (ds, dt) of
                (Abs b1, Abs b2) ->
                    lunbind2 b1 b2 $ \(Just (_, s', _, t')) -> unif' th (s', t')
                (Abs b, t') ->
                    lunbind b $ \(x, s') -> unif' th (s', addApp t' (V x))
                (s', Abs b) ->
                    lunbind b $ \(x, t') -> unif' th (addApp s' (V x), t')
                (s', t') -> cases th (s', t')
                where
                    addApp (App t xs) v = App t (xs ++ [v])
                    addApp t v = App t [v]

        cases th (s, t) = case (strip s, strip t) of
            ((F _F, xm), (F _G, yn)) -> flexflex _F xm _G yn th
            ((F _F, xm), _)          -> flexrigid _F xm t th
            (_, (F _G, yn))          -> flexrigid _G yn s th
            ((a, sm), (b, tn))       -> rigidrigid a sm b tn th

        rigidrigid a sm b tn th =
            if a /= b then throwError "rigidrigid fail"
            else do
                pra  <- prTerm a
                prsm <- prTerms sm
                prb  <- prTerm b
                prtn <- prTerms tn
                prth <- prTheta th
                liftIO $ putStrLn $ "(2) rigidrigid (" ++ pra ++ ", [" ++ prsm ++
                    "], " ++ prb ++ ", [" ++ prtn ++ "], " ++ prth ++ ")"

                foldM unif' th (zip sm tn)

-- use parser
unifP :: String -> String -> IO ()
unifP s1 s2 = 
    case parser s1 of
        Left e1  -> putStrLn $ show e1
        Right t1 ->
            case parser s2 of
                Left e2  -> putStrLn $ show e2
                Right t2 -> do
                    str <- prUnif t1 t2
                    putStrLn str


-- Print

prTerm :: LFresh m => Term -> m String
prTerm (F x) = return $ "#" ++ show x
prTerm (V x) = return $ show x
prTerm (C x) = return $ "_" ++ x
prTerm (App t []) = prTerm t
prTerm (App t ts) = do
    t' <- prTerm t
    ts' <- prTerms ts
    return $ t' ++ "(" ++ ts' ++ ")"
prTerm (Abs b) = prAbs [] (Abs b)
    where
        prAbs ids (Abs b) = do
            lunbind b $ \(x, t) -> prAbs (ids ++ [x]) t
        prAbs ids t = (++) <$> return ("L" ++ prIDs ids ++ ".") <*> prTerm t

prIDs :: [ID] -> String
prIDs [] = ""
prIDs (x:[]) = show x
prIDs (x:xs) = show x ++ "," ++ prIDs xs

prTerms :: LFresh m => [Term] -> m String
prTerms [] = return ""
prTerms (x:[]) = prTerm x
prTerms (x:xs) = do
    x'  <- prTerm x
    xs' <- prTerms xs
    return $ x' ++ "," ++ xs'

prTheta :: LFresh m => Theta -> m String
prTheta t = do { str <- prTheta' t; return $ "{" ++ str }
    where
        prTheta' [] = return "}"
        prTheta' ((id, t):[]) = do
            t' <- prTerm t
            return $ show id ++ " -> " ++ t' ++ "}"
        prTheta' ((id, t):ss) = do
            t'  <- prTerm t
            ss' <- prTheta' ss
            return $ show id ++ " -> " ++ t' ++ ", " ++ ss'

-- prUnif :: Term -> Term -> String
prUnif t1 t2 = runLFreshMT $ do
    th <- runExceptT $ unif t1 t2
    case th of
        Left e -> return e
        Right th' -> prTheta th'


-- parser

-- BNF
-- expr = 'L' IDs '.' term | term
-- term = factor '(' terms ')'
-- factor = '(' expr ')' | literal
-- literal = var | constant
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
    return $ foldr (\id t -> Abs $ bind id t) t ids
    <|> term

pIDs :: Parser [ID]
pIDs = do
    id <- string2Name <$> pString
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
literal = pConstant <|> pVar

pConstant :: Parser Term
pConstant = do
    spaces >> char '_' >> spaces
    id <- pString
    spaces
    return $ C id

pVar :: Parser Term
pVar = do
    spaces
    id <- string2Name <$> pString
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
