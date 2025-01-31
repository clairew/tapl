module UntypedLC where 
import qualified Data.Set as Set
import Data.List (elemIndex)
data Term = Var String | Lam String Term | App Term Term deriving (Show, Eq) 

-- S combinator
s = Lam "x" (Lam "y" (Lam "z"
    (App
        (App (Var "x") (Var "z"))
        (App (Var "y") (Var "z")))))
-- K combinator
k = Lam "x" (Lam "y" (Var "x"))
-- I combinator
i = Lam "x" (Var "x")
-- Omega
omega = Lam "x" (App (Var "x") (Var "x"))

class Numeral a where
    fromInt :: Int -> a
    succNum :: a -> a  
    predNum :: a -> a
    addNum :: a -> a -> a
    multNum :: a -> a -> a
    expNum :: a -> a -> a

newtype Church = Church Term deriving (Show, Eq) 

instance Numeral Church where 
    fromInt n = Church (church n)
--    succNum n = chuchSucc (church n) 

church :: Int -> Term
church 0 = Lam "f" $ Lam "x" $ Var "x"
church n = Lam "f" $ Lam "x" $ foldr (\_ t -> App (Var "f") t) (Var "x") [1..n]

churchSucc :: Term -> Term
churchSucc n = Lam "f" $ Lam "x" $ App (Var "f") (App (App n (Var "f")) (Var "x"))

-- ghci > churchSucc zero
-- Lam "f" (Lam "x" (App (Var "f") (App (App (Lam "f" (Lam "x" (Var "x"))) (Var "f")) (Var "x"))))
-- hm.. I should use my eval function! 
-- eval $ churchSucc zero
-- Lam "f" (Lam "x" (App (Var "f") (Var "x")))
-- ghci> eval $ church 1
-- Lam "f" (Lam "x" (App (Var "f") (Var "x")))
-- ghci> eval $ churchSucc (church 0)
-- Lam "f" (Lam "x" (App (Var "f") (Var "x")))

-- for pred, we have to use pairs to get the previous number. Thanks Kleene!
-- I realize that the K combinator returns the first variable in a pair, so we can use that too.

pair :: Term 
pair = Lam "x" $ Lam "y" $ Lam "f" $ App (App (Var "f") (Var "x")) (Var "y")

first :: Term 
first = Lam "p" $ App (Var "p") (Lam "x" $ Lam "y" $ Var "x")

second :: Term
second = Lam "p" $ App (Var "p") (Lam "x" $ Lam "y" $ Var "y")

alphaConvert :: String -> String -> Term -> Term 
alphaConvert fromString toString (Var x) = if fromString == x then Var toString else Var x 
alphaConvert fromString toString (Lam v t) = if fromString == v then Lam toString $ alphaConvert fromString toString t else Lam v $ alphaConvert fromString toString t 
alphaConvert fromString toString (App t1 t2) = App (alphaConvert fromString toString t1) (alphaConvert fromString toString t2)

-- substitution, naive approach on TAPL p. 69
substitute0 :: String -> Term -> Term -> Term
-- substitute all instances of variable name x with term s in the term v
substitute0 x s (Var v) = if x == v then s else Var v
substitute0 x s (Lam v t) = Lam v $ substitute0 x s t
substitute0 x s (App t1 t2) = App (substitute0 x s t1) (substitute0 x s t2)

-- exploring why substitute0 doesn't work 
-- 
-- [x -> (Lam z.zw)](Lam y.x) = Lam y.Lam z.zw 
-- example = Lam "y" (Var "x")
-- replace = Lam "z" (App (Var "z") (Var "w"))
-- result = substitute0 "x" replace example
-- ghci> result
-- Lam "y" (Lam "z" (App (Var "z") (Var "w"))) 
-- 
-- [x -> y](Lam x.x) = Lam x.y
-- example = Lam "x" (Var "x") 
-- replace = Var "y"
-- result = substitute0 "x" replace example
-- ghci> result
-- Lam "x" (Var "y")
-- this breaks because identify function should be the same regardless of the names of bound variables! 
-- this version doesn't check for free variables or bound variables. 
-- we can replace free variables but can't replace bound variables.

-- substitution attempt 2, p. 70
-- differs from first attempt because it stops substitution when it binds to the same variable.  
substitute1 :: String -> Term -> Term -> Term
substitute1 x s (Var v) = if x == v then s else Var v
substitute1 x s (Lam v t) = if v == x then Lam v t else Lam v $ substitute1 x s t
substitute1 x s (App t1 t2) = App (substitute1 x s t1) (substitute1 x s t2) 
-- [x -> z](Lam z. x) = Lam z.z
-- example = Lam "z" (Var "x")
-- replace = Var "z"
-- result = substitute1 "x" replace example
-- ghci> result
-- Lam "z" (Var "z") -> this is wrong because we end up making Lam z. x into an identity function.

-- in order to avoid variable capture, we need to know what the free variables are! 
-- given a term, return the free vars  
freeVars :: Term -> Set.Set String
freeVars (Var v) = Set.singleton v -- if it's just Var v, return v.
freeVars (Lam v t) = Set.delete v (freeVars t) -- remove bound variable v, call free vars on its bound term
freeVars (App t1 t2) = Set.union (freeVars t1) (freeVars t2) -- union of the free variables from t1 and t2

-- but when variable capture happens, we can use an alpha conversion to rename the bound variable. We have to find a fresh variable. This is kind of annoying because I'd have to generate a fresh variable name and keep track of names that are already used - I realize this is why De Bruijn indices are useful.

-- given base variable name and set of variables to avoid, create infinite list of names and take the first one that isn't in the set of variables to avoid.
freshVar :: String -> Set.Set String -> String
freshVar x vars = head $ filter (\v -> Set.notMember v vars) $ map (\n -> x ++ replicate n '\'') [1..]


-- example = Lam "z" (Var "x")
-- free = freeVars example
-- ghci> free
-- fromList ["x"]
-- example = Lam "x" (App (Var "x") (Var "y"))
-- free = freeVars example 
-- ghci> free 
-- fromList ["y"]
-- example = App (Lam "x" (App (Var "x") (Var "y"))) (Var "z") 
-- free = freeVars example
-- ghci>free
-- fromList ["y","z"]

-- finally, the REAL substitution! 
substitute :: String -> Term -> Term -> Term 
substitute x s (Var v) = if x == v then s else Var v
substitute x s (Lam v t) = 
    if v == x then 
        Lam v t 
    else if Set.notMember v (freeVars s) then 
        Lam v $ substitute x s t 
    else 
        let fresh = freshVar v (freeVars s) 
        in Lam fresh $ substitute x s (substitute v (Var fresh) t) 
substitute x s (App t1 t2) = App (substitute x s t1) (substitute x s t2)

--example = Lam "z" (Var "x")
--replace = Var "y"
--result = substitute "x" replace example
--ghci> result
--Lam "z" (Var "y")

--example = Lam "x" (Var "x") 
--replace = Var "y"
--result = substitute "x" replace example
--ghci> result
--Lam "x" (Var "x")

-- putting it all together in evaluation

isVal :: Term -> Bool
isVal (Var _) = True
isVal (Lam _ _) = True
isVal (App _ _) = False

-- one step of evaluation at a time 
-- implements evaluation rules from Figure 5-3
eval1 :: Term -> Maybe Term
eval1 (Var x) = Nothing
eval1 (Lam x t) = Nothing
eval1 (App t1 t2) =
    case (eval1 t1, eval1 t2, t1, isVal t2) of 
    (Just t1', _, _, _) -> Just (App t1' t2)
    (Nothing, Just t2', _, _) -> Just (App t1 t2')
    (Nothing, Nothing, Lam x t12, True) -> Just (substitute x t2 t12)
    _ -> Nothing
   
-- keeps evaluating using eval1 till normal form 
eval :: Term -> Term
eval (Var v)     = Var v
eval (Lam v t)   = Lam v (eval t)
eval (App t1 t2) = case eval1 (App t1 t2) of 
    Nothing -> App t1 t2
    Just t' -> eval t'

-- a term is in normal form if it can't be reduced further
isNormalForm :: Term -> Bool
isNormalForm (Var _) = True -- variables are always in normal form 
isNormalForm (Lam v t) = isNormalForm t -- for lambdas, need to check if its body is normal 
isNormalForm (App (Lam v t) t2) = False
isNormalForm (App t1 t2) = isNormalForm t1 && isNormalForm t2 


data DBTerm = DBVar Int | DBLam DBTerm | DBApp DBTerm DBTerm deriving (Show, Eq)

-- d is current binding depth 
-- c is how much to shift by 
shift :: Int -> Int -> DBTerm -> DBTerm
shift d c (DBVar i) = if i < c then DBVar i else DBVar (i+d)
shift d c (DBLam t) = DBLam $ shift d (c+1) t
shift d c (DBApp t1 t2) = DBApp (shift d c t1) (shift d c t2) 

-- ghci> shift 1 0 (DBVar 0)
-- DBVar 1

-- don't shift bound variables
-- ghci> shift 1 1 (DBVar 0)
-- DBVar 0

-- ghci> shift 2 0 (DBLam (DBVar 1))
-- DBLam (DBVar 3)

-- ghci> shift 1 0 (DBApp (DBVar 0) (DBVar 1))
-- DBApp (DBVar 1) (DBVar 2)

-- helper function for getting the indice given a context (list of variable names)
go :: [String] -> Term -> DBTerm
go context (Var v) = case elemIndex v context of
    Just i -> DBVar i
    Nothing -> DBVar (length context)
go context (Lam v t) = DBLam $ go context t
go context (App t1 t2) = DBApp (go context t1) (go context t2)

-- given a named term, convert to de bruijn term
toDB :: Term -> DBTerm
toDB (Var v) = go [] (Var v)
toDB (Lam v t) = DBLam $ go [v] t
toDB (App t1 t2) = DBApp (toDB t1) (toDB t2) 

-- using figure 6.2.4
-- substitute variable s with variable number j in the given term
dbSubst :: Int -> DBTerm -> DBTerm -> DBTerm
dbSubst j (DBVar s) (DBVar k) = if j == k then (DBVar s) else (DBVar k)
dbSubst j (DBVar s) (DBLam t) = DBLam $ dbSubst (j+1) (shift 1 0 (DBVar s)) t
dbSubst j (DBVar s) (DBApp t1 t2) = DBApp (dbSubst j (DBVar s) t1) (dbSubst j (DBVar s) t2)

-- ghci> dbSubst 0 (DBVar 1) (DBVar 1)
-- DBVar 1
-- ghci> dbSubst 0 (DBVar 1) (DBVar 0)
-- DBVar 1
-- ghci> dbSubst 0 (DBVar 1) (DBLam (DBVar 0))
-- DBLam (DBVar 0)
-- ghci> dbSubst 0 (DBVar 1) (DBLam (DBVar 1))
-- DBLam (DBVar 2)
-- ghci> dbSubst 0 (DBVar 1) (DBApp (DBVar 0) (DBVar 2))
-- DBApp (DBVar 1) (DBVar 2)

-- fromDB :: DBTerm -> Term 


