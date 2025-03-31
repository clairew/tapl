module FSub where 

import qualified Data.Set as Set
import qualified Data.Map as Map
import Debug.Trace
import Control.Monad.State

data Type
    = TVar String
    | TArrow Type Type
    | TForall String Type Type
    | TExists String Type Type
    | TUnit
    | TNat
    | TAns
    | TBool
    | TTop
    deriving (Show, Eq)

data Term
    = Var String
    | Lam String Type Term
    | App Term Term
    | TyAbs String Type Term
    | TyApp Term Type
    | Pack Type Term Type 
    | Unpack String String Term Term 
    | Unit
    | Zero
    | Succ Term
    | IsZero Term
    | Pred Term
    | Yes
    | No
    | TTrue
    | TFalse
    | TIf Term Term Term
    deriving (Show, Eq)

type Constraint = (Type, Type)
type ConstraintSet = [Constraint]
type FreshVarSeq = [String]

data Context = Context
    { termVars :: [(String, Type)]
    , typeVars :: [(String, Type)] -- String is the var name and Type is its bound  
    } deriving (Show, Eq)

emptyContext :: Context
emptyContext = Context [] []

extendContext :: String -> Type -> Context -> Context
extendContext x t (Context terms types) = Context ((x, t):terms) types

extendTypeVar :: String -> Type -> Context -> Context
extendTypeVar a bound (Context terms types) = Context terms ((a,bound):types) 

lookupVar :: String -> Context -> Maybe Type
lookupVar x (Context terms _) = lookup x terms

lookupTypeVar :: String -> Context -> Maybe Type 
lookupTypeVar a (Context _ types) = lookup a types

typeVarInContext :: String -> Context -> Bool
typeVarInContext a (Context _ types) = any ((==) a . fst) types 

freshVar :: String -> Set.Set String -> String
freshVar x vars = head $ filter (\v -> Set.notMember v vars) $ map (\n -> x ++ replicate n '\'') [1..]

freeTypeVars :: Type -> Set.Set String
freeTypeVars (TVar a) = Set.singleton a
freeTypeVars (TArrow t1 t2) = Set.union (freeTypeVars t1) (freeTypeVars t2)
freeTypeVars (TForall a bound t) = Set.union (freeTypeVars bound) (Set.delete a (freeTypeVars t)) 
freeTypeVars (TExists a bound t) = Set.union (freeTypeVars bound) (Set.delete a (freeTypeVars t))
freeTypeVars TUnit = Set.empty
freeTypeVars TNat = Set.empty
freeTypeVars TAns = Set.empty
freeTypeVars TBool = Set.empty
freeTypeVars TTop = Set.empty

freeTermVars :: Term -> Set.Set String
freeTermVars (Var x) = Set.singleton x
freeTermVars (Lam x _ e) = Set.delete x (freeTermVars e)
freeTermVars (App e1 e2) = Set.union (freeTermVars e1) (freeTermVars e2)
freeTermVars (TyAbs _ _ e) = freeTermVars e
freeTermVars (TyApp e _) = freeTermVars e
freeTermVars Unit = Set.empty
freeTermVars Zero = Set.empty
freeTermVars (Succ e) = freeTermVars e
freeTermVars (Pred e) = freeTermVars e
freeTermVars (IsZero e) = freeTermVars e
freeTermVars TTrue = Set.empty
freeTermVars TFalse = Set.empty
freeTermVars (TIf e1 e2 e3) = Set.unions [freeTermVars e1, freeTermVars e2, freeTermVars e3]

substType :: String -> Type -> Type -> Type
substType a s (TVar b)
    | a == b = s
    | otherwise = TVar b
substType a s (TArrow t1 t2) = TArrow (substType a s t1) (substType a s t2)
substType a s (TForall v bound t)
    | a == v = TForall v bound t
    | otherwise = if Set.notMember v (freeTypeVars s) then TForall v (substType a s bound) (substType a s t)
        else let fresh = freshVar v (Set.union (freeTypeVars t) (freeTypeVars s))
        in TForall fresh (substType a s bound) (substType a s (substType v (TVar fresh) t))
substType a s (TExists v bound t) 
    | a == v = TExists v bound t 
    | otherwise = if Set.notMember v (freeTypeVars s) then TExists v (substType a s bound) (substType a s t)
        else let fresh = freshVar v (Set.union (freeTypeVars t) (freeTypeVars s))
        in TExists fresh (substType a s bound) (substType a s (substType v (TVar fresh) t))
substType _ _ TUnit = TUnit
substType _ _ TNat = TNat
substType _ _ TBool = TBool
substType _ _ TAns = TAns
substType _ _ TTop = TTop


substTypeInTerm :: String -> Type -> Term -> Term
substTypeInTerm a s (Var x) = Var x
substTypeInTerm a s (Lam x t e) = Lam x (substType a s t) (substTypeInTerm a s e)
substTypeInTerm a s (TyAbs x bound t)
    | a == x = TyAbs x bound t
    | otherwise =
        let bindsX = case s of
                TForall y _ _ | x == y -> True
                _ -> False
            needsRename = bindsX || Set.member x (freeTypeVars s)
        in if needsRename
            then
                let fresh = freshVar x (Set.union (freeTypeVars s) (Set.singleton a))
                    t' = substTypeInTerm x (TVar fresh) t
                in TyAbs fresh (substType a s bound) (substTypeInTerm a s t')
            else
                TyAbs x (substType a s bound) (substTypeInTerm a s t)
substTypeInTerm a s (App e1 e2) = App (substTypeInTerm a s e1) (substTypeInTerm a s e2)
substTypeInTerm a s (TyApp t typ) = TyApp (substTypeInTerm a s t) (substType a s typ)
substTypeInTerm _ _ Unit = Unit
substTypeInTerm _ _ Zero = Zero
substTypeInTerm a s (Succ e) = Succ (substTypeInTerm a s e)
substTypeInTerm a s (Pred e) = Pred (substTypeInTerm a s e)
substTypeInTerm a s (IsZero e) = IsZero (substTypeInTerm a s e)
substTypeInTerm _ _ Yes = Yes
substTypeInTerm _ _ No = No
substTypeInTerm _ _ TTrue = TTrue
substTypeInTerm _ _ TFalse = TFalse
substTypeInTerm a s (TIf e1 e2 e3) = TIf (substTypeInTerm a s e1) (substTypeInTerm a s e2) (substTypeInTerm a s e3)

substTerm :: String -> Term -> Term -> Term
substTerm x s (Var v)
    | x == v = s
    | otherwise = Var v
substTerm x s (Lam v t u)
    | x == v = Lam v t u
    | otherwise =
        if Set.notMember v $ freeTermVars s
            then Lam v t (substTerm x s u)
        else
            let fresh = freshVar x (Set.union(freeTermVars s) (freeTermVars u))
            in Lam fresh t (substTerm x s (substTerm v (Var fresh) u))
substTerm x s (TyAbs v bound t) =
    if Set.notMember x $ freeTermVars t
            then TyAbs v bound t
            else TyAbs v bound (substTerm x s t)
substTerm x s (App t1 t2) = App (substTerm x s t1) (substTerm x s t2)
substTerm x s (TyApp t typ) = TyApp (substTerm x s t) typ
substTerm _ _ Unit = Unit
substTerm _ _ Zero = Zero
substTerm _ _ Yes = Yes
substTerm _ _ No = No
substTerm _ _ TTrue = TTrue
substTerm _ _ TFalse = TFalse
substTerm x s (Succ e) = Succ (substTerm x s e)
substTerm x s (Pred e) = Pred (substTerm x s e)
substTerm x s (IsZero e) = IsZero (substTerm x s e)
substTerm x s (TIf e1 e2 e3) = TIf (substTerm x s e1) (substTerm x s e2) (substTerm x s e3)

isWellFormedType :: Context -> Type -> Bool
isWellFormedType ctx (TVar v) = typeVarInContext v ctx
isWellFormedType ctx (TArrow t1 t2) = isWellFormedType ctx t1 && isWellFormedType ctx t2
isWellFormedType ctx (TForall v bound t) =
    isWellFormedType ctx bound && 
    let extendedCtx = extendTypeVar v bound ctx
    in isWellFormedType extendedCtx t
isWellFormedType ctx (TExists v bound t) = 
    isWellFormedType ctx bound && 
    let extendedCtx = extendTypeVar v bound ctx 
    in isWellFormedType extendedCtx t
isWellFormedType _ TUnit = True
isWellFormedType _ TNat = True
isWellFormedType _ TAns = True
isWellFormedType _ TBool = True
isWellFormedType _ TTop = True

typeOf :: Context -> Term -> Maybe Type
typeOf ctx (Var v) = lookupVar v ctx
typeOf ctx (Lam x t1 v) = do
    if not $ isWellFormedType ctx t1
        then Nothing
        else do
            let ctx' = extendContext x t1 ctx
            t2 <- typeOf ctx' v
            return (TArrow t1 t2)
typeOf ctx (TyAbs v bound t1) = do
    if not $ isWellFormedType ctx bound 
        then Nothing
    else do 
        let ctx' = extendTypeVar v bound ctx
        t2 <- typeOf ctx' t1
        return (TForall v bound t2)
typeOf ctx (App t1 t2) = do
    t1' <- typeOf ctx t1
    t2' <- typeOf ctx t2
    case t1' of
        TArrow t11 t12 ->
            if isSubtype ctx t2' t11
                then Just t12
                else Nothing
        _ -> Nothing
typeOf ctx (TyApp t1 t2) = do
    if not $ isWellFormedType ctx t2
        then Nothing
    else do
        t1' <- typeOf ctx t1
        case t1' of
            TForall v bound body ->
                if isSubtype ctx t2 bound 
                    then Just (substType v t2 body)
                    else Nothing
            _ -> Nothing
typeOf _ Unit = Just TUnit
typeOf _ Zero = Just TNat
typeOf ctx (Succ e) = do
    t <- typeOf ctx e
    if isSubtype ctx t TNat then Just TNat else Nothing
typeOf ctx (Pred e) = do
    t <- typeOf ctx e
    if isSubtype ctx t TNat then Just TNat else Nothing
typeOf ctx (IsZero e) = do
    t <- typeOf ctx e
    if isSubtype ctx t TNat then Just TAns else Nothing
typeOf _ Yes = Just TAns
typeOf _ No = Just TAns
typeOf _ TTrue = Just TBool
typeOf _ TFalse = Just TBool
typeOf ctx (TIf e1 e2 e3) = do
    t1 <- typeOf ctx e1
    t2 <- typeOf ctx e2
    t3 <- typeOf ctx e3
    if isSubtype ctx t1 TBool && (isSubtype ctx t2 t3 || isSubtype ctx t3 t2)
        then if isSubtype ctx t2 t3
            then Just t3
            else Just t2
        else Nothing
typeOf ctx (Pack witness_type term exists_type) = do
    if not $ isWellFormedType ctx exists_type
        then Nothing
        else case exists_type of
            TExists a bound body -> do
                if not $ isSubtype ctx witness_type bound
                    then Nothing
                    else do
                        term_type <- typeOf ctx term 
                        let expected_type = substType a witness_type body 
                        if isSubtype ctx term_type expected_type 
                            then Just exists_type
                            else Nothing
            _ -> Nothing
typeOf ctx (Unpack a x packed body) = do
    packed_type <- typeOf ctx packed
    case packed_type of
        TExists a' bound t -> do 
            let ctx' = extendTypeVar a bound $ extendContext x t ctx 
            body_type <- typeOf ctx' body
            if Set.member a (freeTypeVars body_type)
                then Nothing
                else Just body_type
        _ -> Nothing

isSubtype :: Context -> Type -> Type -> Bool
isSubtype _ s TTop = True
isSubtype _ v t | v == t = True
isSubtype ctx (TVar a) t = 
    case lookupTypeVar a ctx of
        Just bound -> isSubtype ctx bound t 
        Nothing -> False
isSubtype ctx (TArrow s1 s2) (TArrow t1 t2) = isSubtype ctx t1 s1 && isSubtype ctx s2 t2    
isSubtype ctx (TForall a1 s1 s2) (TForall b1 t1 t2) = 
    isSubtype ctx t1 s1 && 
    let ctx' = extendTypeVar a1 t1 ctx 
    in isSubtype ctx' s2 (substType b1 (TVar a1) t2)
isSubtype ctx (TExists a1 s1 s2) (TExists b1 t1 t2) = 
    isSubtype ctx t1 t2 &&
    let ctx' = extendTypeVar a1 s1 ctx
    in isSubtype ctx' (substType b1 (TVar a1) t2) s2 
isSubtype _ _ _ = False

isVal :: Term -> Bool
isVal (Lam _ _ _) = True
isVal (TyAbs _ _ _) = True
isVal (Var _) = True
isVal (Succ e) = isVal e
isVal (Pred e) = isVal e
isVal Unit = True
isVal Zero = True
isVal Yes = True
isVal No = True
isVal TTrue = True
isVal TFalse = True
isVal (Pack _ term _) = isVal term
isVal _ = False

eval1 :: Term -> Maybe Term
eval1 (Var _) = Nothing
eval1 (Lam _ _ _) = Nothing
eval1 (TyAbs _ _ _) = Nothing
eval1 (App t1 t2) = case t1 of
    Lam x typ t12 | isVal t2 -> Just (substTerm x t2 t12)
    _ -> case eval1 t1 of
        Just t1' -> Just (App t1' t2)
        Nothing -> case eval1 t2 of
            Just t2' | isVal t1 -> Just (App t1 t2')
            Nothing -> Nothing
eval1 (Succ t) = case eval1 t of
    Just t' -> Just (Succ t')
    Nothing -> Nothing
eval1 (Pred t) = case eval1 t of
    Just t' -> Just (Pred t')
    Nothing -> Nothing
eval1 (IsZero t) = case t of
     Zero -> Just Yes
     Succ nv | isVal nv -> Just No
     _ -> case eval1 t of
         Just t' -> Just (IsZero t')
         Nothing -> Nothing
eval1 (TyApp (TyAbs v _ t12) t2) = Just (substTypeInTerm v t2 t12)
eval1 (TyApp t typ) = case eval1 t of
    Just t' -> Just (TyApp t' typ)
    Nothing -> Nothing
eval1 (TIf e1 e2 e3) =
    case e1 of
        TTrue -> Just e2
        TFalse -> Just e3
        _ -> case eval1 e1 of
                Just e1' -> Just (TIf e1' e2 e3)
                Nothing -> Nothing
eval1 (Pack witness_type term target_type) = 
    case eval1 term of
        Just term' -> Just (Pack witness_type term' target_type)
        Nothing -> Nothing
eval1 (Unpack a x packed body) =
    case packed of
        Pack witness_type value _ | isVal value -> 
            Just (substTerm x value (substTypeInTerm a witness_type body))
        _ -> case eval1 packed of
            Just packed' -> Just (Unpack a x packed' body)
            Nothing -> Nothing
eval1 _ = Nothing

eval :: Term -> Term
eval t = case eval1 t of
    Nothing -> t
    Just t' -> eval t'

sBool :: Type
sBool = TForall "X" TTop
          (TForall "T" (TVar "X")
            (TForall "F" (TVar "X")
              (TArrow (TVar "T")
                (TArrow (TVar "F") (TVar "X")))))

sTrue :: Type
sTrue = TForall "X" TTop
          (TForall "T" (TVar "X")
            (TForall "F" (TVar "X")
              (TArrow (TVar "T")
                (TArrow (TVar "F") (TVar "T"))))) 

sFalse :: Type
sFalse = TForall "X" TTop
          (TForall "T" (TVar "X")
            (TForall "F" (TVar "X")
              (TArrow (TVar "T")
                (TArrow (TVar "F") (TVar "F")))))

tru :: Term 
tru = TyAbs "X" TTop 
    (TyAbs "T" (TVar "X") 
        (TyAbs "F" (TVar "X")
            (Lam "t" (TVar "T")
                (Lam "f" (TVar "F")
                    (Var "t")))))

fls :: Term 
fls = TyAbs "X" TTop 
    (TyAbs "T" (TVar "X") 
        (TyAbs "F" (TVar "X")
            (Lam "t" (TVar "T")
                (Lam "f" (TVar "F")
                    (Var "f")))))

notftTerm :: Term
notftTerm = Lam "b" sFalse
              (TyAbs "X" TTop
                (TyAbs "T" (TVar "X")
                  (TyAbs "F" (TVar "X")
                    (Lam "t" (TVar "T")
                      (Lam "f" (TVar "F")
                        (TyApp
                          (TyApp
                            (TyApp (Var "b") (TVar "X"))
                            (TVar "F"))
                          (TVar "T")
                        `App` (Var "f")
                        `App` (Var "t")))))))

nottfTerm :: Term
nottfTerm = Lam "b" sTrue
              (TyAbs "X" TTop
                (TyAbs "T" (TVar "X")
                  (TyAbs "F" (TVar "X")
                    (Lam "t" (TVar "T")
                      (Lam "f" (TVar "F")
                        (TyApp
                          (TyApp
                            (TyApp (Var "b") (TVar "X"))
                            (TVar "F"))
                          (TVar "T")
                        `App` (Var "f")
                        `App` (Var "t")))))))

notftType :: Type
notftType = TArrow sFalse sTrue 

nottfType :: Type 
nottfType = TArrow sTrue sFalse 

-- minimalXFreeSupertype :: Set.Set String -> Context -> Type -> Type
