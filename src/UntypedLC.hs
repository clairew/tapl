module UntypedLC where 

data Term = Var String | Lam String Term | App Term Term deriving (Show, Eq) 

-- I combinator
i = Lam "x" (Var "x")
-- K combinator
k = Lam "x" (Lam "y" (Var "x"))
-- S combinator
s = Lam "x" (Lam "y" (Lam "z"
    (App
        (App (Var "x") (Var "z"))
        (App (Var "y") (Var "z")))))
-- Omega
omega = Lam "x" (App (Var "x") (Var "x"))

-- 
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
-- -
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
