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
