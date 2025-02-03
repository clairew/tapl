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

-- if we don't use Maybe, then the catch all condition would result in an infinite evaluaiton (stuck). So Nothing in this function would indicate stuck. 
--eval1Old :: Term -> Maybe Term 
--eval1Old (TIf TTrue t2 t3) = Just t2
--eval1Old (TIf TFalse t2 t3) = Just t3
--eval1Old (TIf t1 t2 t3) = case eval1Old t1 of 
--    Just t1' -> Just (TIf t1' t2 t3)
--    _ -> Nothing

-- eval1Old without Maybe, resulting in infinite evaluation 
eval1Old :: Term -> Term
eval1Old (TIf TTrue t2 t3) = t2
eval1Old (TIf TFalse t2 t3) = t3
eval1Old (TIf t1 t2 t3) = case eval1Old t1 of 
    t1' -> TIf t1' t2 t3
-- ghci> eval1Old (TIf TZero TTrue TFalse)
-- TIf *** Exception: ArithmeticExpr.hs:(53,1)-(56,24): Non-exhaustive patterns in function eval1Old
eval1Old (TSucc t1) = case eval1Old t1 of 
   t1' -> TSucc t1'
eval1Old (TPred TZero) = TZero
eval1Old (TPred (TSucc nv1)) | isNumericVal nv1 = nv1
eval1Old (TPred t1) = case eval1Old t1 of 
    t1' -> TPred t1'
eval1Old (TIsZero TZero) = TTrue
eval1Old (TIsZero (TSucc nv1)) | isNumericVal nv1 = TFalse
eval1Old (TIsZero t1) = case eval1Old t1 of 
    t1' -> TIsZero t1'

eval1 :: Term -> Term
eval1 (TIf TTrue t2 t3) = t2
eval1 (TIf TFalse t2 t3) = t3
eval1 (TIf t1 t2 t3)
    | isBadBool t1 = TWrong
    | otherwise = case eval1 t1 of 
    t1' -> TIf t1' t2 t3
    _ -> TWrong
-- eval1 (TIf t1 t2 t3) = (\t1' -> TIf t1' t2 t3) <$>eval1 t1
{- case eval1 t1 of 
    Just t1' -> Just (TIf t1' t2 t3)
    Nothing -> Nothing
    -}

eval1 (TSucc t1)
    | isBadNat t1 = TWrong
    | isVal t1 = TSucc t1
    | otherwise = TSucc (eval1 t1) 
eval1 (TPred (TSucc nv1)) | isNumericVal nv1 = nv1
eval1 (TPred TZero) = TZero
eval1 (TPred t1)
    | isBadBool t1 = TWrong
    | otherwise = case eval1 t1 of
    TZero -> TZero
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



