module FOmega where

import qualified Data.Set as Set
import qualified Data.Map as Map
import Debug.Trace
import Control.Monad.State

data Type
    = TVar String
    | TArrow Type Type
    | TForall String Type
    | TAbs String Kind Type
    | TApp Type Type
    deriving (Show, Eq)

data Term
    = Var String
    | Lam String Type Term
    | App Term Term
    | TyAbs String Kind Term
    | TyApp Term Type 
    deriving (Show, Eq)

data Kind
    = KStar
    | KArrow Kind Kind
    deriving (Show, Eq)

data Context = Context
    { termVars :: [(String, Type)]
    , typeVars :: Map.Map String Kind
    } deriving (Show, Eq)

emptyContext :: Context
emptyContext = Context [] Map.empty

extendContext :: String -> Type -> Context -> Context 
extendContext var typ (Context terms types) = Context ((var, typ):terms) types 

extendTypeVar :: String -> Kind -> Context -> Context 
extendTypeVar var k (Context terms types) = Context terms (Map.insert var k types)

lookupVar :: String -> Context -> Maybe Type
lookupVar x (Context terms _) = lookup x terms

lookupTypeVarKind :: String -> Context -> Maybe Kind
lookupTypeVarKind x (Context _ types) = Map.lookup x types 

typeVarInContext :: String -> Context -> Bool
typeVarInContext a (Context _ types) = Map.member a types

freshVar :: String -> Set.Set String -> String
freshVar x vars = head $ filter (\v -> Set.notMember v vars) $ map (\n -> x ++ replicate n '\'') [1..]

freeTypeVars :: Type -> Set.Set String
freeTypeVars (TVar a) = Set.singleton a
freeTypeVars (TArrow t1 t2) = Set.union (freeTypeVars t1) (freeTypeVars t2)
freeTypeVars (TForall a t) = Set.delete a (freeTypeVars t)
freeTypeVars (TApp t1 t2) = Set.union (freeTypeVars t1) (freeTypeVars t2)
freeTypeVars (TAbs a _ t) = Set.delete a (freeTypeVars t)

freeTermVars :: Term -> Set.Set String
freeTermVars (Var x) = Set.singleton x
freeTermVars (Lam x _ e) = Set.delete x (freeTermVars e)
freeTermVars (App e1 e2) = Set.union (freeTermVars e1) (freeTermVars e2)
freeTermVars (TyAbs _ _ e) = freeTermVars e
freeTermVars (TyApp e _) = freeTermVars e

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
substType a s (TAbs v k t)
    | a == v = TAbs v k t
    | otherwise = if Set.notMember v (freeTypeVars s) then TAbs v k (substType a s t)
        else let fresh = freshVar v (Set.union (freeTypeVars t) (freeTypeVars s))
        in TAbs fresh k (substType a s (substType v (TVar fresh) t))
substType a s (TApp t1 t2) = TApp (substType a s t1) (substType a s t2)

substTypeInTerm :: String -> Type -> Term -> Term
substTypeInTerm a s (Var x) = Var x
substTypeInTerm a s (Lam x t e) = Lam x (substType a s t) (substTypeInTerm a s e)
substTypeInTerm a s (TyAbs x k t)
 | a == x = TyAbs x k t
 | otherwise =
     let bindsX = case s of
             TForall y _ | x == y -> True
             _ -> False
         needsRename = bindsX || Set.member x (freeTypeVars s)
     in if needsRename
         then
             let fresh = freshVar x (Set.union (freeTypeVars s) (Set.singleton a))
                 t' = substTypeInTerm x (TVar fresh) t
             in TyAbs fresh k (substTypeInTerm a s t')
         else
             TyAbs x k (substTypeInTerm a s t)
substTypeInTerm a s (App e1 e2) = App (substTypeInTerm a s e1) (substTypeInTerm a s e2)
substTypeInTerm a s (TyApp t typ) = TyApp (substTypeInTerm a s t) (substType a s typ)

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
substTerm x s (TyAbs v k t) =
 if Set.notMember x $ freeTermVars t
         then TyAbs v k t
         else TyAbs v k (substTerm x s t)
substTerm x s (App t1 t2) = App (substTerm x s t1) (substTerm x s t2)
substTerm x s (TyApp t typ) = TyApp (substTerm x s t) typ

isVal :: Term -> Bool
isVal (Lam _ _ _) = True
isVal (TyAbs _ _ _) = True
isVal (Var _) = True

eval1 :: Term -> Maybe Term
eval1 (App t1 t2) = case eval1 t1 of
    Just t1' -> Just (App t1' t2)
    Nothing -> if isVal t1
        then App t1 <$> eval1 t2
        else Nothing
eval1 (App (Lam x typ body) v2) | isVal v2 = Just (substTerm x v2 body)
eval1 (App t1 t2) = case eval1 t1 of
    Just t1' -> Just (App t1' t2)
    Nothing -> if isVal t1 
        then App t1 <$> eval1 t2
        else Nothing
eval1 (TyApp t typ) = case eval1 t of
    Just t' -> Just (TyApp t' typ)
    Nothing -> Nothing
eval1 (TyApp (TyAbs x k body) typ) = Just (substTypeInTerm x typ body)
eval1 _ = Nothing

eval :: Term -> Term
eval t = case eval1 t of
    Just t' -> eval t'
    Nothing -> t

computeType :: Type -> Maybe Type
computeType (TApp (TAbs x _ body) arg) = Just (substType x arg body)
computeType _ = Nothing

simplifyType :: Type -> Type 
simplifyType tyT = 
    let tyT' = case tyT of
                 TApp t1 t2 -> TApp (simplifyType t1) t2
                 _ -> tyT
    in case computeType tyT' of
         Just tyT'' -> simplifyType tyT''
         Nothing -> tyT'

typeEquiv :: Type -> Type -> Bool
typeEquiv tyS tyT = 
    let tyS' = simplifyType tyS
        tyT' = simplifyType tyT
    in case (tyS', tyT') of 
        (TVar i, TVar j) -> i == j
        (TArrow s1 s2, TArrow t1 t2) -> typeEquiv s1 t1 && typeEquiv s2 t2 
        (TForall x1 s2, TForall x2 t2) ->
            let t2' = substType x2 (TVar x1) t2 
            in typeEquiv s2 t2'
        (TAbs x1 k1 t1, TAbs x2 k2 t2) -> 
            k1 == k2 && typeEquiv t1 (substType x2 (TVar x1) t2)
        (TApp s1 s2, TApp t1 t2) ->
            typeEquiv s1 t1 && typeEquiv s2 t2
        _ -> False

kindOf :: Context -> Type -> Maybe Kind 
kindOf ctx (TVar v) = lookupTypeVarKind v ctx
kindOf ctx (TArrow t1 t2) = do
    k1 <- kindOf ctx t1
    k2 <- kindOf ctx t2 
    if k1 == KStar && k2 == KStar
        then return KStar
        else Nothing
kindOf ctx (TApp t1 t2) = do 
    k1 <- kindOf ctx t1 
    k2 <- kindOf ctx t2 
    case k1 of
        KArrow k1' k2' -> if k1' == k2 then return k2' else Nothing
        _ -> Nothing
kindOf ctx (TAbs v k1 typ) = do 
    let extended = extendTypeVar v k1 ctx
    k2 <- kindOf extended typ 
    return (KArrow k1 k2)
kindOf ctx (TForall x typ) = do
    let extended = extendTypeVar x KStar ctx 
    k <- kindOf extended typ
    if k == KStar then return KStar else Nothing

typeOf :: Context -> Term -> Maybe Type
typeOf ctx (Var v) = lookupVar v ctx
typeOf ctx (Lam x t1 e) = do 
    k <- kindOf ctx t1
    if k /= KStar then Nothing else do 
            let ctx' = extendContext x t1 ctx
            t2 <- typeOf ctx' e 
            return $ TArrow t1 t2
typeOf ctx (App t1 t2) = do 
    t1' <- typeOf ctx t1 
    t2' <- typeOf ctx t2
    case simplifyType t1' of 
        TArrow t11 t12 -> 
            if typeEquiv t11 t2' then return t2'
                else Nothing
typeOf ctx (TyAbs v k t) = do
    let extended = extendTypeVar v k ctx 
    t' <- typeOf extended t 
    return $ TForall v t'
typeOf ctx (TyApp t typ) = 
    case kindOf ctx typ of
        Just k -> do 
            t' <- typeOf ctx t
            case simplifyType t' of 
                TForall v body -> return $ substType v typ body
                _ -> Nothing

parallelReduce :: Type -> Type
parallelReduce (TVar x) = TVar x 
parallelReduce (TArrow t1 t2) = TArrow (parallelReduce t1) (parallelReduce t2) 
parallelReduce (TForall x t) = TForall x (parallelReduce t) 
parallelReduce (TAbs x k t) = TAbs x k (parallelReduce t)
parallelReduce (TApp (TAbs x _ t) arg) = substType x (parallelReduce arg) (parallelReduce t) 
parallelReduce (TApp t1 t2) = TApp (parallelReduce t1) (parallelReduce t2)

typeEquivParallel :: Type -> Type -> Bool 
typeEquivParallel s t = 
    let s' = parallelReduce s 
        t' = parallelReduce t 
    in if s == t then True else
        if s == s' && t == t' then False 
            else typeEquivParallel s' t'

normalizeParallel :: Type -> Type 
normalizeParallel t = 
    let t' = parallelReduce t 
    in if t == t' then t 
        else normalizeParallel t'
        
