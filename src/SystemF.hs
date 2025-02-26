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
