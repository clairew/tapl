module TypedLC where
import qualified Data.Set as Set
import Debug.Trace
import qualified Data.Map as Map
data Type = TBool 
    | TArrow Type Type
    | TUnit
    | TAns
    | TProd Type Type
    | TTop
    | TRecord [(String, Type)]
    | TArr [(Type, Type)]
    | TRef Type
    | TNat
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
          | Record [(String, Term)]
          | Ref Term -- ref t
          | Deref Term -- !t
          | Assign Term Term -- t:=t
          | Loc String -- l (store location)
          | Zero
          | Succ Term
          | Pred Term
          | IsZero Term
          | If Term Term Term
          deriving (Show, Eq)

nat :: Int -> Term
nat 0 = Zero
nat n = Succ (nat (n-1))

factType :: Type
factType = TArrow TNat TNat

newtype Context = Context [(String, Type)]

emptyContext :: Context
emptyContext = Context []

extendContext :: String -> Type -> Context -> Context
extendContext name typ (Context ctx) = Context ((name,typ):ctx)

lookupType :: String -> Context -> Maybe Type
lookupType x (Context []) = Nothing
lookupType x (Context ((name,typ):rest)) = if x == name then Just typ else lookupType x (Context rest)

newtype Store = Store (Map.Map String Term)
emptyStore :: Store
emptyStore = Store Map.empty 

extendStore :: String -> Term -> Store -> Store
extendStore loc val (Store s) = Store (Map.insert loc val s)

lookupStore :: String -> Store -> Maybe Term
lookupStore loc (Store s) = Map.lookup loc s

newtype StoreContext = StoreContext (Map.Map String Type) 

emptyStoreContext :: StoreContext
emptyStoreContext = StoreContext Map.empty

extendStoreContext :: String -> Type -> StoreContext -> StoreContext
extendStoreContext loc typ (StoreContext m) = StoreContext $ Map.insert loc typ m

lookupStoreType :: String -> StoreContext -> Maybe Type
lookupStoreType loc (StoreContext s) = Map.lookup loc s 

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
typeOf ctx Zero = Just TNat
typeOf ctx (Succ t) = case typeOf ctx t of
    Just TNat -> Just TNat
    _ -> Nothing
typeOf ctx (Pred t) = case typeOf ctx t of
    Just TNat -> Just TNat
    _ -> Nothing
typeOf ctx (IsZero t) = case typeOf ctx t of
    Just TNat -> Just TAns
    _ -> Nothing
typeOf ctx (If t1 t2 t3) = case typeOf ctx t1 of
    Just TAns -> case (typeOf ctx t2, typeOf ctx t3) of
        (Just t2type, Just t3type) | t2type == t3type -> Just t2type
        _ -> Nothing
    _ -> Nothing

typeOfStore :: Context -> StoreContext -> Term -> Maybe Type
typeOfStore ctx storeCtx (Loc s) = case lookupStoreType s storeCtx of
    Nothing -> Nothing
    Just t' -> Just (TRef t') 
typeOfStore ctx storeCtx (Ref t) = case typeOfStore ctx storeCtx t of
    Nothing -> Nothing
    Just t' -> Just (TRef t')
typeOfStore ctx storeCtx (Deref t) = case typeOfStore ctx storeCtx t of
    Nothing -> Nothing
    Just (TRef t') -> Just t'
typeOfStore ctx storeCtx (Assign t1 t2) = case typeOfStore ctx storeCtx t1 of
    Nothing -> Nothing
    Just (TRef t1') -> case typeOfStore ctx storeCtx t2 of
        Nothing -> Nothing
        Just t2' -> if t1' == t2' then Just TUnit else Nothing 
typeOfStore ctx storeCtx Zero = Just TNat
typeOfStore ctx storeCtx (Succ t) = case typeOfStore ctx storeCtx t of
    Just TNat -> Just TNat
    _ -> Nothing
typeOfStore ctx storeCtx (Pred t) = case typeOfStore ctx storeCtx t of
    Just TNat -> Just TNat
    _ -> Nothing
typeOfStore ctx storeCtx (IsZero t) = case typeOfStore ctx storeCtx t of
    Just TNat -> Just TAns
    _ -> Nothing
typeOfStore ctx storeCtx (If t1 t2 t3) = case typeOfStore ctx storeCtx t1 of
    Just TAns -> case (typeOfStore ctx storeCtx t2, typeOfStore ctx storeCtx t3) of
        (Just t2type, Just t3type) | t2type == t3type -> Just t2type
        _ -> Nothing
    _ -> Nothing
typeOfStore ctx storeCtx t = typeOf ctx t 

isSubtype :: Type -> Type -> Bool
isSubtype t1 TTop = True 
isSubtype t1 t2 | t1 == t2 = True
isSubtype (TRecord fields1) (TRecord fields2) = 
    all (\(name2, type2) -> 
        case lookup name2 fields1 of
            Nothing -> False
            Just type1 -> isSubtype type1 type2) fields2 
isSubtype (TArrow s1 t1) (TArrow s2 t2) = (isSubtype s2 s1) && (isSubtype t1 t2)
isSubtype _ _ = False

freeVars :: Term -> Set.Set String
freeVars (Var v) = Set.singleton v
freeVars (Lam v typ t) = Set.delete v (freeVars t)
freeVars (App t1 t2) = Set.union (freeVars t1) (freeVars t2)
freeVars (Pair t1 t2) = Set.union (freeVars t1) (freeVars t2)
freeVars (Proj1 t) = freeVars t
freeVars (Proj2 t) = freeVars t
freeVars (Record fields) = Set.unions [freeVars t | (_, t) <- fields]
freeVars (Ref t) = freeVars t
freeVars (Deref t) = freeVars t
freeVars (Assign t1 t2) = Set.union (freeVars t1) (freeVars t2)
freeVars (Succ t) = freeVars t
freeVars (Pred t) = freeVars t
freeVars (IsZero t) = freeVars t
freeVars (If t1 t2 t3) = Set.unions [freeVars t1, freeVars t2, freeVars t3]
freeVars Zero = Set.empty
freeVars Yes = Set.empty
freeVars No = Set.empty
freeVars Unit = Set.empty
freeVars (Loc _) = Set.empty

freshVar :: String -> Set.Set String -> String
freshVar x vars = head $ filter (\v -> Set.notMember v vars) $ map (\n -> x ++ replicate n '\'') [1..]

freshLoc :: Store -> String 
freshLoc (Store s) =  head $ filter (\v -> Map.notMember v s) $ map (\n -> "l" ++ replicate n '\'') [1..]

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
subst x s (Pair t1 t2) = Pair (subst x s t1) (subst x s t2)
subst x s (Proj1 t) = Proj1 (subst x s t)
subst x s (Proj2 t) = Proj2 (subst x s t)
subst x s (Record fields) = Record [(l, subst x s t) | (l, t) <- fields]
subst x s (Ref t) = Ref (subst x s t)
subst x s (Deref t) = Deref (subst x s t)
subst x s (Assign t1 t2) = Assign (subst x s t1) (subst x s t2)
subst x s (Succ t) = Succ (subst x s t)
subst x s (Pred t) = Pred (subst x s t)
subst x s (IsZero t) = IsZero (subst x s t)
subst x s (If t1 t2 t3) = If (subst x s t1) (subst x s t2) (subst x s t3)
subst _ _ Zero = Zero
subst _ _ Yes = Yes
subst _ _ No = No
subst _ _ Unit = Unit
subst _ _ (Loc l) = Loc l

isVal :: Term -> Bool
isVal (Lam v typ t) = True
isVal Yes = True
isVal No = True
isVal Unit = True 
isVal (Pair _ _) = True 
isVal Zero = True
isVal (Succ t) | isVal t = True
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
eval1 (Succ t) = case eval1 t of
    Just t' -> Just (Succ t') 
    Nothing -> Nothing
eval1 (Pred t) = case t of
    Zero -> Just Zero
    Succ nv | isVal nv -> Just nv
    _ -> case eval1 t of
        Just t' -> Just (Pred t')
        Nothing -> Nothing
eval1 (IsZero t) = case t of
    Zero -> Just Yes
    Succ nv | isVal nv -> Just No
    _ -> case eval1 t of
        Just t' -> Just (IsZero t')
        Nothing -> Nothing
eval1 (If t1 t2 t3) = case t1 of
    Yes -> Just t2
    No -> Just t3
    _ -> case eval1 t1 of
        Just t1' -> Just (If t1' t2 t3)
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

-- termination example of call by value vs. head reduction
{-omega = App 
    (Lam "x" TAns (App (Var "x") (Var "x")))
    (Lam "x" TAns (App (Var "x") (Var "x")))

divergingTest = App
    (Lam "x" TAns Yes)  -- A function that ignores its argument and returns Yes
    omega-}

-- let's not do this.. can't use propositions as types in hs.   
--isHereditarilyTerminating :: Term -> Type -> Bool
--isHereditarilyTerminating m typ = case typ of
{-    TUnit -> case evalhead m of 
        Unit -> True
        _ -> False
    TAns -> case evalhead m of 
        Yes -> True
        No -> True 
        _ -> False 
isHereditarilyTerminating m (TProd t1 t2) = case evalhead m of
    Pair m1 m2 -> isHereditarilyTerminating m1 t1 && isHereditarilyTerminating m2 t2 
    _ -> False -}

inDomain :: String -> Store -> Bool
inDomain loc (Store s) = Map.member loc s

eval1store :: Term -> Store -> Maybe (Term, Store)
eval1store (App t1 t2) s = 
    case eval1store t1 s of -- E-APP1 
        Just (t1', s') -> Just (App t1' t2, s')
        Nothing ->
            if isVal t1 then
                case eval1store t2 s of -- E-APP2
                    Just (t2', s') -> Just (App t1 t2', s')
                    Nothing ->
                        case t1 of -- E-APPABS 
                            Lam x typ t12 | isVal t2 -> Just (subst x t2 t12, s)
                            _ -> Nothing
            else Nothing
eval1store (Ref v) s | isVal v = -- E-REFV 
    let l = freshLoc s
    in if not (inDomain l s)
        then Just (Loc l, extendStore l v s)
        else Nothing
eval1store (Ref t) s = -- E-REF 
    case eval1store t s of 
        Just (t', s') -> Just (Ref t', s')
        Nothing -> Nothing
eval1store (Deref (Loc l)) s = case lookupStore l s of -- E-DEREFLOC 
        Just v | isVal v -> Just (v, s) 
        _ -> Nothing
eval1store (Deref t) s = -- E-DEREF
    case eval1store t s of
        Just (t', s') -> Just (Deref t', s')
        Nothing -> Nothing
eval1store (Assign t1 t2) s =
    case eval1store t1 s of
        Just (t1', s') -> Just (Assign t1' t2, s')
        Nothing -> case t1 of
            Loc l -> case eval1store t2 s of
                Just (t2', s') -> Just (Assign (Loc l) t2', s')
                Nothing | isVal t2 -> Just (Unit, extendStore l t2 s)
                Nothing -> Nothing
            _ -> Nothing
eval1store (Succ t) s =
    case eval1store t s of
        Just (t', s') -> Just (Succ t', s')
        Nothing -> Nothing
eval1store (Pred t) s =
    case eval1store t s of
        Just (t', s') -> Just (Pred t', s')
        Nothing -> case t of
            Zero -> Just (Zero, s)           
            Succ nv | isVal nv -> Just (nv, s) 
            _ -> Nothing
eval1store (IsZero t) s =
    case eval1store t s of
        Just (t', s') -> Just (IsZero t', s')
        Nothing -> case t of
            Zero -> Just (Yes, s)
            Succ nv | isVal nv -> Just (No, s)
            _ -> Nothing
eval1store (If t1 t2 t3) s = 
    case eval1store t1 s of
        Just (t1', s') -> Just (If t1' t2 t3, s')  
        Nothing -> case t1 of
            Yes -> Just (t2, s)   
            No -> Just (t3, s)    
            _ -> Nothing
eval1store _ s = Nothing
evalStore :: Term -> Store -> Term
evalStore t s = case eval1store t s of
    Nothing -> t
    Just (t', s') -> evalStore t' s'


mult :: Term
mult =
    Lam "n" TNat (
    Lam "m" TNat (
        If (IsZero (Var "n"))
           Zero
           (App
             (App plus (Var "m"))
             (App
               (App mult (Pred (Var "n")))
               (Var "m")))))

plus :: Term
plus =
    Lam "n" TNat (
    Lam "m" TNat (
        If (IsZero (Var "n"))
           (Var "m")
           (Succ (App
                   (App plus (Pred (Var "n")))
                   (Var "m")))))


fact :: Term
fact = 
    Lam "n" TNat (
        If (IsZero (Var "n"))
           (Succ Zero)                        -- then branch: return 1
           (App                               -- else branch: n * fact(n-1)
             (App mult (Var "n"))
             (App fact (Pred (Var "n")))))

factRef :: Term
factRef =
    -- create a reference to store the factorial function
    App
        (Lam "r" (TRef (TArrow TNat TNat))
            -- store factorial in the reference
            (Assign (Var "r") fact))
        (Ref fact)  -- initialize with factorial

testFactRef :: Term
testFactRef = evalStore factRef emptyStore

