module TypedLC where
import qualified Data.Set as Set
import Debug.Trace
data Type = TBool 
    | TArrow Type Type
    | TUnit
    | TAns
    | TProd Type Type 
    deriving (Show, Eq)

data Term = Var String
          | Lam String Type Term  
          | App Term Term
          | Yes
          | No
          | Unit
          | Pair Term Term 
          | Proj1 Term
          | Proj2 Term
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
typeOf ctx Yes = Just TAns
typeOf ctx No = Just TAns
typeOf ctx Unit = Just TUnit
typeOf ctx (Pair m1 m2) = case typeOf ctx m1 of
    Nothing -> Nothing
    Just m1' -> case typeOf ctx m2 of
        Nothing -> Nothing
        Just m2' -> Just (TProd m1' m2') 
typeOf ctx (Proj1 m1) = case typeOf ctx m1 of
    Nothing -> Nothing
    Just (TProd t1 _) -> Just t1

typeOf ctx (Proj2 m2) = case typeOf ctx m2 of
    Nothing -> Nothing
    Just (TProd _ t2) -> Just t2

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
subst x s t = t

isVal :: Term -> Bool
isVal (Lam v typ t) = True
isVal Yes = True
isVal No = True
isVal Unit = True 
isVal (Pair _ _) = True 
isVal _ = False


-- call by value strategy
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
eval1 _ = Nothing
-- head reduction strategy for Tait's method 
eval1head :: Term -> Maybe Term
eval1head (Proj1(Pair m1 m2)) = Just m1
eval1head (Proj2(Pair m1 m2)) = Just m2
eval1head (Proj1 m) = case eval1head m of
    Just m1' -> Just (Proj1 m1')
    Nothing -> Nothing
eval1head (Proj2 m) = case eval1head m of
    Just m2' -> Just (Proj2 m2')
    Nothing -> Nothing
eval1head (App (Lam x typ m) m2) = Just (subst x m2 m) 
eval1head (App m1 m2) = case eval1head m1 of 
    Just m1' -> Just (App m1' m2)
    Nothing -> Nothing
eval1head _ = Nothing

eval :: Term -> Term
eval t = case eval1 $ traceShowId t of
    Nothing -> t 
    Just t' -> eval t'

evalhead :: Term -> Term
evalhead t = case eval1head $ traceShowId t of
    Nothing -> t 
    Just t' -> evalhead t'

omega = App 
    (Lam "x" TAns (App (Var "x") (Var "x")))
    (Lam "x" TAns (App (Var "x") (Var "x")))

divergingTest = App
    (Lam "x" TAns Yes)  -- A function that ignores its argument and returns Yes
    omega

isHereditarilyTerminating :: Term -> Type -> Bool
isHereditarilyTerminating m typ = case typ of
    TUnit -> case evalhead m of 
        Unit -> True
        _ -> False
    TAns -> case evalhead m of 
        Yes -> True
        No -> True 
        _ -> False 
isHereditarilyTerminating m (TProd t1 t2) = case m of
    Pair m1 m2 -> isHereditarilyTerminating m1 t1 && isHereditarilyTerminating m2 t2 
    _ -> False

--isHereditarilyTerminating m (TArrow t1 t2) = case m of
