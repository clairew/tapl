module SystemF where

import qualified Data.Set as Set
import qualified Data.Map as Map
import Debug.Trace
import Control.Monad.State

data Type
    = TVar String
    | TArrow Type Type
    | TForall String Type
    | TUnit
    | TNat
    | TAns
    | TBool
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

-- from TAPL 22.3.9
freshVarPreAlloc :: FreshVarSeq -> (Type, FreshVarSeq)
freshVarPreAlloc [] = error "Exhausted the supply of fresh variable names"
freshVarPreAlloc (v:vs) = (TVar v, vs) 

freeTypeVars :: Type -> Set.Set String 
freeTypeVars (TVar a) = Set.singleton a
freeTypeVars (TArrow t1 t2) = Set.union (freeTypeVars t1) (freeTypeVars t2)
freeTypeVars (TForall a t) = Set.delete a (freeTypeVars t)
freeTypeVars TUnit = Set.empty
freeTypeVars TNat = Set.empty
freeTypeVars TAns = Set.empty
freeTypeVars TBool = Set.empty

freeTermVars :: Term -> Set.Set String
freeTermVars (Var x) = Set.singleton x
freeTermVars (Lam x _ e) = Set.delete x (freeTermVars e)
freeTermVars (App e1 e2) = Set.union (freeTermVars e1) (freeTermVars e2)
freeTermVars (TyAbs _ e) = freeTermVars e
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
substType a s (TForall v t) 
    | a == v = TForall v t
    | otherwise = if Set.notMember v (freeTypeVars s) then TForall v (substType a s t)
        else let fresh = freshVar v (Set.union (freeTypeVars t) (freeTypeVars s))
        in TForall fresh (substType a s (substType v (TVar fresh) t))
substType _ _ TUnit = TUnit
substType _ _ TNat = TNat
substType _ _ TBool = TBool
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
substTerm x s (TyAbs v t) =  
    if Set.notMember x $ freeTermVars t 
            then TyAbs v t  
            else TyAbs v (substTerm x s t)
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
isWellFormedType ctx (TForall v t) = 
    let extendedCtx = extendTypeVar v ctx 
    in isWellFormedType extendedCtx t
isWellFormedType _ TUnit = True
isWellFormedType _ TNat = True
isWellFormedType _ TAns = True
isWellFormedType _ TBool = True

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
        TArrow t11 t12 -> if t2' == t11 then Just t12 else Nothing 
        _ -> Nothing
typeOf ctx (TyApp t typ) = do 
    if not $ isWellFormedType ctx typ
        then Nothing
    else do
        t12 <- typeOf ctx t
        case t12 of
            TForall v body -> Just (substType v typ body)
            _ -> Nothing
typeOf _ Unit = Just TUnit
typeOf _ Zero = Just TNat
typeOf ctx (Succ e) = do 
    t <- typeOf ctx e
    if t == TNat then Just TNat else Nothing
typeOf ctx (Pred e) = do 
    t <- typeOf ctx e
    if t == TNat then Just TNat else Nothing
typeOf ctx (IsZero e) = do 
    t <- typeOf ctx e 
    if t == TNat then Just TNat else Nothing
typeOf _ Yes = Just TAns
typeOf _ No = Just TAns
typeOf _ TTrue = Just TBool
typeOf _ TFalse = Just TBool
typeOf ctx (TIf e1 e2 e3) = do
    t1 <- typeOf ctx e1
    t2 <- typeOf ctx e2
    t3 <- typeOf ctx e3
    if t1 == TBool && t2 == t3
        then Just t2
        else Nothing

isVal :: Term -> Bool
isVal (Lam _ _ _) = True
isVal (TyAbs _ _) = True
isVal (Var _) = True
isVal (Succ e) = isVal e
isVal (Pred e) = isVal e
isVal Unit = True
isVal Zero = True
isVal Yes = True
isVal No = True
isVal TTrue = True
isVal TFalse = False
isVal _ = False

eval1 :: Term -> Maybe Term
eval1 (Var _) = Nothing
eval1 (Lam _ _ _) = Nothing 
eval1 (TyAbs _ _) = Nothing
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
eval1 (TyApp (TyAbs v t12) t2) = Just (substTypeInTerm v t2 t12)
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
eval1 _ = Nothing

eval :: Term -> Term 
eval t = case eval1 t of
    Nothing -> t
    Just t' -> eval t'

isNormalForm :: Term -> Bool
isNormalForm t = case eval1 t of
    Nothing -> True
    Just _ -> False

stepsToNormalForm :: Term -> Int 
stepsToNormalForm t = case eval1 t of
    Nothing -> 0 
    Just t' -> 1 + stepsToNormalForm t'

-- set-based approach where we generate fresh type variables not in the VarSet
-- type VarSet = Set.Set String
{--inferConstraints :: Context -> Term -> (Type, ConstraintSet, VarSet)
inferConstraints ctx (Var v) = case lookupVar v ctx of
    Just t -> (t, [], Set.empty)
    Nothing -> error $ "Unbound variable: " ++ v
inferConstraints ctx (Lam x t1 t2) =
    let extendedCtx = extendContext x t1 ctx
        (bodytype, constraints, vars) = inferConstraints extendedCtx t2
     in (TArrow t1 bodytype, constraints, vars)
--}

-- sequence approach from tapl 22.3.9 
-- we have a sequence of available fresh type variables
{--inferConstraints :: Context -> Term -> FreshVarSeq -> (Type, ConstraintSet, FreshVarSeq)
inferConstraints ctx (Var v) freshVars = case lookupVar v ctx of
    Just t -> (t, [], freshVars)
    Nothing -> error $ "Unbound variable: " ++ v
inferConstraints ctx (Lam x t1 t2) freshVars = 
    let extendedCtx = extendContext x t1 ctx 
        (bodytype, constraints, vars') = inferConstraints extendedCtx t2 freshVars 
     in (TArrow t1 bodytype, constraints, vars')
--}

-- generator approach from tapl 22.3.10 
-- use a recursive generator for fresh type variables
data UVarGen = NextUVar String UVarGen

initialUVarGen :: UVarGen 
initialUVarGen = go 0 
    where go n = NextUVar ("?X_" ++ show n) (go (n+1))

freshGenVar :: UVarGen -> (Type, UVarGen) 
freshGenVar (NextUVar name nextGen) = (TVar name, nextGen)

-- state monad approach
freshStateVar :: State String Type
freshStateVar = do 
    current <- get 
    put (current ++ "'")
    return $ TVar current 

inferNatOperation :: Context -> Term -> Type -> UVarGen -> (Type, ConstraintSet, UVarGen)
inferNatOperation ctx subterm resultType freshVarGen = 
    let (subtype, constraints, freshVarGen1) = inferConstraints ctx subterm freshVarGen
        newConstraints = constraints ++ [(subtype, TNat)] 
    in
        (resultType, newConstraints, freshVarGen1)

inferConstraints :: Context -> Term -> UVarGen -> (Type, ConstraintSet, UVarGen)
inferConstraints ctx (Var v) freshVarGen = case lookupVar v ctx of
    Just t -> (t, [], freshVarGen)
    Nothing -> error $ "Unbound variable: " ++ v
inferConstraints ctx (Lam x t1 t2) freshVarGen =
    let extendedCtx = extendContext x t1 ctx 
        (bodytype, constraints, freshVarGen') = inferConstraints extendedCtx t2 freshVarGen 
     in (TArrow t1 bodytype, constraints, freshVarGen')
inferConstraints ctx (App t1 t2) freshVarGen =
    let (type1, constraints1, freshVarGen1) = inferConstraints ctx t1 freshVarGen
        (type2, constraints2, freshVarGen2) = inferConstraints ctx t2 freshVarGen1
        (resultType, freshVarGen3) = freshGenVar freshVarGen2
        newConstraint = (type1, TArrow type2 resultType)
        allConstraints = constraints1 ++ constraints2 ++ [newConstraint]
    in 
        (resultType, allConstraints, freshVarGen3)
inferConstraints ctx Zero freshVarGen = (TNat, [], freshVarGen)
{-inferConstraints ctx (Succ e) freshVarGen =  
    let (type1, constraints1, freshVarGen1) = inferConstraints ctx e freshVarGen
        newConstraints = constraints1 ++ [(type1, TNat)]
    in 
        (TNat, newConstraints, freshVarGen1)-}
-- CT-Succ, CT-Pred, CT-IsZero result in duplicating code so instead use a helper to generalize the rules.
inferConstraints ctx (Succ e) freshVarGen = inferNatOperation ctx e TNat freshVarGen
inferConstraints ctx (Pred e) freshVarGen = inferNatOperation ctx e TNat freshVarGen
inferConstraints ctx (IsZero e) freshVarGen = inferNatOperation ctx e TAns freshVarGen
inferConstraints ctx TTrue freshVarGen = (TBool, [], freshVarGen)
inferConstraints ctx TFalse freshVarGen = (TBool, [], freshVarGen)
inferConstraints ctx (TIf e1 e2 e3) freshVarGen =
    let (e1type, e1constraints, freshVarGen1) = inferConstraints ctx e1 freshVarGen
        (e2type, e2constraints, freshVarGen2) = inferConstraints ctx e2 freshVarGen1
        (e3type, e3constraints, freshVarGen3) = inferConstraints ctx e3 freshVarGen2
        condConstraint = [(e1type, TBool)]
        branchConstraint = [(e2type, e3type)]
        allConstraints = e1constraints ++ e2constraints ++ e3constraints ++ condConstraint ++ branchConstraint
    in
        (e2type, allConstraints, freshVarGen3)
