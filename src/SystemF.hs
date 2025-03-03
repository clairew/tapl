module SystemF where

import qualified Data.Set as Set
import qualified Data.Map as Map
import Debug.Trace

data Type
    = TVar String
    | TArrow Type Type
    | TForall String Type
    | TUnit
    | TNat
    | TAns
    deriving (Show, Eq)

data Term 
    = Var String
    | Lam String Type Term
    | App Term Term 
    | TyAbs String Term 
    | TyApp Term Type 
    | Unit
    | Zero
    | Succ Term
    | IsZero Term
    | Yes
    | No
    deriving (Show, Eq)

data Context = Context
    { termVars :: [(String, Type)]
    , typeVars :: Set.Set String
    } deriving (Show, Eq)

emptyContext :: Context
emptyContext = Context [] Set.empty

extendContext :: String -> Type -> Context -> Context
extendContext x t (Context terms types) = Context ((x, t):terms) types

extendTypeVar :: String -> Context -> Context
extendTypeVar a (Context terms types) = Context terms (Set.insert a types)

lookupVar :: String -> Context -> Maybe Type 
lookupVar x (Context terms _) = lookup x terms

typeVarInContext :: String -> Context -> Bool
typeVarInContext a (Context _ types) = Set.member a types

freshVar :: String -> Set.Set String -> String
freshVar x vars = head $ filter (\v -> Set.notMember v vars) $ map (\n -> x ++ replicate n '\'') [1..]

freeTypeVars :: Type -> Set.Set String 
freeTypeVars (TVar a) = Set.singleton a
freeTypeVars (TArrow t1 t2) = Set.union (freeTypeVars t1) (freeTypeVars t2)
freeTypeVars (TForall a t) = Set.delete a (freeTypeVars t)
freeTypeVars TUnit = Set.empty
freeTypeVars TNat = Set.empty
freeTypeVars TAns = Set.empty

freeTermVars :: Term -> Set.Set String
freeTermVars (Var x) = Set.singleton x
freeTermVars (Lam x _ e) = Set.delete x (freeTermVars e)
freeTermVars (App e1 e2) = Set.union (freeTermVars e1) (freeTermVars e2)
freeTermVars (TyAbs _ e) = freeTermVars e
freeTermVars (TyApp e _) = freeTermVars e
freeTermVars Unit = Set.empty
freeTermVars Zero = Set.empty
freeTermVars (Succ e) = freeTermVars e
freeTermVars (IsZero e) = freeTermVars e

substType :: String -> Type -> Type -> Type  
substType a s (TVar b) 
    | a == b = s
    | otherwise = TVar b
substType a s (TArrow t1 t2) = TArrow (substType a s t1) (substType a s t2)
substType a s (TForall v t) 
    | a == v = TForall v t
    | otherwise = if Set.notMember v (freeTypeVars s) then TForall v (substType a s t)
        else let fresh = freshVar v (Set.union (freeTypeVars t) (freeTypeVars s))
        in TForall fresh (substType a s (substType v (TVar fresh) t))
substType a s (TUnit) = TUnit
substType a s (TNat) = TNat
substType _ _ TAns = TAns

substTypeInTerm :: String -> Type -> Term -> Term 
substTypeInTerm a s (Var x) = Var x
substTypeInTerm a s (Lam x t e) = Lam x (substType a s t) (substTypeInTerm a s e)
substTypeInTerm a s (TyAbs x t) 
    | a == x = TyAbs x t 
    | otherwise = 
        if Set.notMember x $ freeTypeVars s 
            then TyAbs x (substTypeInTerm a s t)
            else
                let fresh = freshVar x (Set.union(freeTypeVars s) (Set.fromList [a]))
                in TyAbs fresh (substTypeInTerm a s (substTypeInTerm x (TVar fresh) t))
substTypeInTerm a s (App e1 e2) = App (substTypeInTerm a s e1) (substTypeInTerm a s e2) 
substTypeInTerm a s (TyApp t typ) = TyApp (substTypeInTerm a s t) (substType a s typ)
substTypeInTerm _ _ Unit = Unit
substTypeInTerm _ _ Zero = Zero
substTypeInTerm a s (Succ e) = Succ (substTypeInTerm a s e)
substTypeInTerm a s (IsZero e) = IsZero (substTypeInTerm a s e)
substTypeInTerm _ _ Yes = Yes
substTypeInTerm _ _ No = No

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
substTerm x s (TyAbs v t) =  
    if Set.notMember x $ freeTermVars t 
            then TyAbs v t  
            else TyAbs v (substTerm x s t)
substTerm x s (App t1 t2) = App (substTerm x s t1) (substTerm x s t2)
substTerm x s (TyApp t typ) = TyApp (substTerm x s t) typ
substTerm _ _ Unit = Unit
substTerm _ _ Zero = Zero 
substTerm x s (Succ e) = Succ (substTerm x s e)
substTerm x s (IsZero e) = IsZero (substTerm x s e)

isWellFormedType :: Context -> Type -> Bool 
isWellFormedType ctx (TVar v) = typeVarInContext v ctx
isWellFormedType ctx (TArrow t1 t2) = isWellFormedType ctx t1 && isWellFormedType ctx t2
isWellFormedType ctx (TForall v t) = 
    let extendedCtx = extendTypeVar v ctx 
    in isWellFormedType extendedCtx t
isWellFormedType _ TUnit = True
isWellFormedType _ TNat = True
isWellFormedType _ TAns = True

typeOf :: Context -> Term -> Maybe Type 
typeOf ctx (Var v) = lookupVar v ctx 
typeOf ctx (Lam x t1 v) = do 
    if not $ isWellFormedType ctx t1 
        then Nothing 
        else do 
            let ctx' = extendContext x t1 ctx 
            t2 <- typeOf ctx' v
            return (TArrow t1 t2)
typeOf ctx (TyAbs v t1) = do 
    let ctx' = extendTypeVar v ctx 
    t2 <- typeOf ctx' t1
    return (TForall v t2)
typeOf ctx (App t1 t2) = do
    t1' <- typeOf ctx t1 
    t2' <- typeOf ctx t2 
    case t1' of
        TArrow t11 t12 -> if t2' == t12 then Just t12 else Nothing 
        _ -> Nothing
typeOf ctx (TyApp t typ) = do 
    if not $ isWellFormedType ctx typ
        then Nothing
    else do
        t12 <- typeOf ctx t
        case t12 of
            TForall v t12 -> Just (substType v typ t12)
            _ -> Nothing
typeOf _ Unit = Just TUnit
typeOf _ Zero = Just TNat
typeOf ctx (Succ e) = do 
    t <- typeOf ctx e
    if t == TNat then Just TNat else Nothing
typeOf ctx (IsZero e) = do 
    t <- typeOf ctx e 
    if t == TNat then Just TNat else Nothing
typeOf _ Yes = Just TAns
typeOf _ No = Just TAns
