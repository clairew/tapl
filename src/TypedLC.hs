module TypedLC where
import qualified Data.Set as Set
data Type = TBool | TArrow Type Type deriving (Show, Eq)

data Term = Var String
          | Lam String Type Term  
          | App Term Term
          deriving (Show, Eq)

newtype Context = Context [(String, Type)]

emptyContext :: Context
emptyContext = Context []

extendContext :: String -> Type -> Context -> Context
extendContext name typ (Context ctx) = Context ((name,typ):ctx)

lookupType :: String -> Context -> Maybe Type
lookupType x (Context []) = Nothing
lookupType x (Context ((name,typ):rest)) = if x == name then Just typ else lookupType x (Context rest)

typeOf :: Context -> Term -> Maybe Type
typeOf ctx (Var v) = case (lookupType v ctx) of
    Nothing -> Nothing
    Just typ -> Just typ
typeOf ctx (Lam v typ t) = let extended = extendContext v typ ctx in
    case typeOf extended t of
    Nothing -> Nothing
    Just t' -> Just(TArrow typ t')  
typeOf ctx (App f arg) = case typeOf ctx f of
    Nothing -> Nothing 
    Just (TArrow t11 t12) -> case typeOf ctx arg of
        Nothing -> Nothing
        Just t2 -> if t2 == t11 then Just t12 else Nothing

freeVars :: Term -> Set.Set String
freeVars (Var v) = Set.singleton v
freeVars (Lam v typ t) = Set.delete v (freeVars t)
freeVars (App t1 t2) = Set.union (freeVars t1) (freeVars t2)

freshVar :: String -> Set.Set String -> String
freshVar x vars = head $ filter (\v -> Set.notMember v vars) $ map (\n -> x ++ replicate n '\'') [1..]

subst :: String  -- variable to replace
      -> Term    -- term to substitute in
      -> Term    -- target term
      -> Term    -- resulting term
subst x s (Var v) = if x == v then s else Var v
subst x s (Lam v typ t) = if x == v then Lam v typ t
    else if Set.notMember v (freeVars s) then
        Lam v typ (subst x s t)
    else 
        let fresh = freshVar v (freeVars s)
        in Lam fresh typ $ subst x s (subst v (Var fresh) t)
subst x s (App t1 t2) = App (subst x s t1) (subst x s t2)

isVal :: Term -> Bool
isVal (Lam v typ t) = True
isVal _ = False

eval1 :: Term -> Maybe Term
eval1 (Var _) = Nothing
eval1 (Lam _ _ _) = Nothing
eval1 (App t1 t2) = case t1 of
    Lam x typ t12 | isVal t2 -> Just (subst x t2 t12)    
    _ -> case eval1 t1 of
        Just t1' -> Just (App t1' t2)
        Nothing -> case eval1 t2 of 
            Just t2' | isVal t1 -> Just (App t1 t2')
            Nothing -> Nothing

eval :: Term -> Term
eval t = case eval1 t of
    Nothing -> Nothing
    Just t' -> eval1 t'
