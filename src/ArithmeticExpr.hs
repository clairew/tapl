module ArithmeticExpr (
    Term(..),
    isNumericVal,
    isVal,
    eval1,
    eval2
) where 

data Term = 
    TTrue 
    | TFalse 
    | TIf Term Term Term 
    | TZero 
    | TSucc Term 
    | TPred Term 
    | TIsZero Term 
    | TWrong
    deriving (Show, Eq)

isNumericVal :: Term -> Bool
isNumericVal TZero = True
isNumericVal (TSucc t) = isNumericVal t
isNumericVal _ = False

isVal :: Term -> Bool 
isVal TTrue = True 
isVal TFalse = True 
isVal t | isNumericVal t = True 
isVal _ = False

isBadNat :: Term -> Bool
isBadNat TWrong = True
isBadNat TTrue = True
isBadNat TFalse = True
isBadNat _ = False 

isBadBool :: Term -> Bool 
isBadBool TWrong = True
isBadBool val = case isNumericVal val of 
    True -> True
    _ -> False
isBadBool _ = False


eval1 :: Term -> Term
eval1 (TIf TTrue t2 t3) = t2
eval1 (TIf TFalse t2 t3) = t3
eval1 (TIf t1 t2 t3)
    | isBadBool t1 = TWrong
    | otherwise = case eval1 t1 of 
    t1' -> (TIf t1' t2 t3)
    _ -> TWrong
-- eval1 (TIf t1 t2 t3) = (\t1' -> TIf t1' t2 t3) <$>eval1 t1
{- case eval1 t1 of 
    Just t1' -> Just (TIf t1' t2 t3)
    Nothing -> Nothing
    -}
--eval1 (TSucc t1) = case eval1 t1 of 
--   t1' -> TSucc t1'
--  _ -> TWrong 
eval1 (TSucc t1)
    | isBadNat t1 = TWrong
    | isVal t1 = TSucc t1
    | otherwise = TSucc (eval1 t1) 
eval1 (TPred (TSucc nv1)) | isNumericVal nv1 = nv1
eval1 (TPred t1)
    | isBadBool t1 = TWrong
    | otherwise = case eval1 t1 of
    t1' -> TPred t1'
    _ -> TWrong
eval1 (TIsZero TZero) = TTrue
eval1 (TIsZero (TSucc nv1)) | isNumericVal nv1 = TFalse
eval1 (TIsZero t1)
    | isBadNat t1 = TWrong
    | otherwise = case eval1 t1 of 
    t1' -> TIsZero t1'
    _ -> TWrong 
eval1 _ = TWrong


-- big step version -- 
eval2 (TIf t1 t2 t3) = case (eval2 t1, eval2 t2, eval2 t3) of 
    (TTrue, t2', _) -> t2'
    (TFalse, _, t3') -> t3'
    _ -> TWrong 

eval2 (TPred t1) = case (eval2 t1) of 
    (TZero) -> TZero
    ((TSucc t1)) -> t1 
    (t1') -> (TPred t1')
    _ -> TWrong 

eval2 (TIsZero t1) = case (eval2 t1) of 
    (TZero) -> TTrue
    ((TSucc t1)) -> TFalse 
    (t1') -> (TIsZero t1') 
    _ -> TWrong 



