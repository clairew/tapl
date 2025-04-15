module TypedLC where
import qualified Data.Set as Set
import Debug.Trace
import qualified Data.Map as Map
import Data.Maybe (isJust, catMaybes)
data Type = TBool 
    | TArrow Type Type
    | TUnit
    | TAns
    | TProd Type Type
    | TTop
    | TBottom
    | TRecord [(String, Type)]
    | TArr [(Type, Type)]
    | TRef Type
    | TNat 
    | TRec String Type
    | TVar String
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
          | Fold Type Term
          | Unfold Term
          | Fix Term
          | Case Term [(String, String, Term)]
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
typeOf ctx (Fold recType@(TRec x bodyType) term) = 
    case typeOf ctx term of
        Just t ->
            let unfolded = substType x recType bodyType
            in if t == unfolded then Just recType else Nothing
        Nothing -> Nothing
typeOf ctx (Unfold term) = 
    case typeOf ctx term of
        Just (TRec x bodyType) -> Just (substType x (TRec x bodyType) bodyType)
        _ -> Nothing
typeOf ctx (Fix t) =
    case typeOf ctx t of
        Just (TArrow t1 t2) | t1 == t2 -> Just t1
        _ -> Nothing
typeOf ctx (Case t branches) = 
  case typeOf ctx t of
    Just (TRecord fields) ->
      let branchTypes = map (\(tag, var, branch) -> 
                             case lookup tag fields of
                               Just fieldType -> 
                                 typeOf (extendContext var fieldType ctx) branch
                               Nothing -> Nothing) branches
      in if all isJust branchTypes && allEqual (catMaybes branchTypes)
         then Just (head (catMaybes branchTypes)) 
         else Nothing
    _ -> Nothing
  where
    allEqual [] = True
    allEqual (x:xs) = all (== x) xs

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
isSubtype TBottom t2 = True
isSubtype t1 TBottom = False
isSubtype t1 t2 | t1 == t2 = True
isSubtype (TRecord fields1) (TRecord fields2) = 
    all (\(name2, type2) -> 
        case lookup name2 fields1 of
            Nothing -> False
            Just type1 -> isSubtype type1 type2) fields2 
isSubtype (TArrow s1 t1) (TArrow s2 t2) = (isSubtype s2 s1) && (isSubtype t1 t2)
isSubtype (TProd s1 s2) (TProd t1 t2) = (isSubtype s1 t1) && (isSubtype s2 t2) 
isSubtype _ _ = False

isReflexive :: Type -> Bool
isReflexive t1 = isSubtype t1 t1 

isTransitive :: Type -> Type -> Type -> Bool
-- if isSubtype s u and isSubtype u t then isSubtype s t
isTransitive s u t = isSubtype s u && isSubtype u t

-- algorithmic subtyping
subtype :: Type -> Type -> Bool
subtype s t = case (s, t) of
    (TNat, TNat) -> True
    (TAns, TAns) -> True
    (TUnit, TUnit) -> True
    (TArrow s1 s2, TArrow t1 t2) -> subtype t1 s1 && subtype s2 t2
    (TProd s1 s2, TProd t1 t2) -> subtype s1 t1 && subtype s2 t2
    (TRecord fields1, TRecord fields2) -> 
        let names1 = Set.fromList [name | (name, _) <- fields1] 
            names2 = Set.fromList [name | (name, _) <- fields2] 
        in Set.isSubsetOf names2 names1 && all(\(name2, type2) ->
            case lookup name2 fields1 of
                Nothing -> False
                Just type1 -> subtype type1 type2)
        fields2
    (_, TTop) -> True
    (TBottom, _) -> True
    _ -> False

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
freeVars (Fold _ t) = freeVars t
freeVars (Unfold t) = freeVars t
freeVars (Fix t) = freeVars t
freeVars (Case t branches) = 
    Set.union 
        (freeVars t)
        (Set.unions [Set.delete var (freeVars branch) | (tag, var, branch) <- branches])

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
subst x s (Fold typ t) = Fold typ (subst x s t)
subst x s (Unfold t) = Unfold (subst x s t)
subst x s (Fix t) = Fix (subst x s t)
subst x s (Case t branches) =
    Case (subst x s t)
        [(tag, var, if x == var 
                    then branch 
                    else if Set.member var (freeVars s)
                         then let fresh = freshVar var (freeVars s)
                              in subst x s (subst var (Var fresh) branch)
                         else subst x s branch) 
         | (tag, var, branch) <- branches]
subst _ _ Zero = Zero
subst _ _ Yes = Yes
subst _ _ No = No
subst _ _ Unit = Unit
subst _ _ (Loc l) = Loc l

substType :: String -> Type -> Type -> Type 
substType x s (TVar y) | x == y = s
substType _ _ (TVar y) = TVar y
substType x s (TRec y t) | x == y = TRec y t
substType x s (TRec y t) = TRec y (substType x s t) 
substType x s (TArrow t1 t2) = TArrow (substType x s t1) (substType x s t2)
substType x s (TProd t1 t2) = TProd (substType x s t1) (substType x s t2)
substType x s (TRef t) = TRef (substType x s t)
substType x s (TRecord fields) = TRecord [(l, substType x s t) | (l, t) <- fields]
substType x s (TArr pairs) = TArr [(substType x s t1, substType x s t2) | (t1, t2) <- pairs]
substType _ _ TBool = TBool
substType _ _ TUnit = TUnit
substType _ _ TNat = TNat
substType _ _ TTop = TTop
substType _ _ TBottom = TBottom
substType _ _ TAns = TAns

isVal :: Term -> Bool
isVal (Lam v typ t) = True
isVal Yes = True
isVal No = True
isVal Unit = True 
isVal (Pair _ _) = True 
isVal Zero = True
isVal (Succ t) | isVal t = True
isVal (Fold _ v) | isVal v = True
isVal (Record _) = True
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
            _ -> Nothing
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
eval1 (Fold typ t) = case eval1 t of
    Just t' -> Just (Fold typ t')
    Nothing -> Nothing
eval1 (Unfold t) = case t of
    Fold _ v | isVal v -> Just v
    _ -> case eval1 t of
        Just t' -> Just (Unfold t')
        Nothing -> Nothing
eval1 (Fix t) = case t of
    Lam x typ body -> Just (subst x (Fix t) body) 
    _ -> case eval1 t of
        Just t' -> Just (Fix t')
        Nothing -> Nothing
eval1 (Case t branches) =
  case t of
    Record fields ->
      case findMatchingBranch fields branches of
        Just (var, value, branch) -> Just (subst var value branch)
        Nothing -> Nothing
    _ -> case eval1 t of
           Just t' -> Just (Case t' branches)
           Nothing -> Nothing
  where
    findMatchingBranch :: [(String, Term)] -> [(String, String, Term)] -> Maybe (String, Term, Term)
    findMatchingBranch _ [] = Nothing
    findMatchingBranch fields ((tag, var, branch):rest) =
      case lookup tag fields of
        Just value -> Just (var, value, branch)
        Nothing -> findMatchingBranch fields rest
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
eval t = case eval1 t of
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

streamType :: Type
streamType = TRec "A" (TArrow TUnit (TProd TNat (TVar "A")))

streamHead :: Term -> Term
streamHead s = Proj1 (App (Unfold s) Unit)

streamTail :: Term -> Term
streamTail s = Proj2 (App (Unfold s) Unit)

fibStream :: Term
fibStream = App (App
        (Fix
            (Lam "f" (TArrow TNat (TArrow TNat streamType)) 
                (Lam "m" TNat 
                    (Lam "n" TNat
                        (Fold streamType 
                            (Lam "_" TUnit
                                (Pair 
                                    (Var "n")
                                        (App
                                            (App (Var "f") (Var "n"))
                                            (App (App plus (Var "m")) (Var "n"))
                                            )
                                        )
                                )
                            )
                        )
                    )
                )
            )
        (nat 0))
    (nat 1)

counterType :: Type
counterType = TRec "C" (TRecord [
    ("get", TNat),
    ("inc", TArrow TUnit (TVar "C")),
    ("dec", TArrow TUnit (TVar "C")),
    ("backup", TArrow TUnit (TVar "C")),
    ("reset", TArrow TUnit (TVar "C"))
    ])

counter :: Term 
counter = App
    (Fix 
        (Lam "f" (TArrow (TRecord[("x", TNat), ("backup", TNat)]) counterType)
            (Lam "s" (TRecord[("x", TNat), ("backup", TNat)])
                (Fold counterType
                    (Record[
                        ("get", Proj1(Record[("1", (Var "x"))])),
                        ("inc", Lam "_" TUnit
                            (App (Var "f")
                                (Record [
                                ("x", Succ (Proj1(Record[("1", (Var "x"))]))),
                                ("backup", Proj2(Record [("2", (Var "x"))]))
                                ])
                            )
                        ),
                        ("dec", Lam "_" TUnit
                            (App (Var "f")
                                (Record [
                                ("x", Succ (Proj1(Record[("1", (Var "x"))]))),
                                ("backup", Proj2(Record [("2", (Var "x"))]))
                                ])
                            )
                        ),
                        ("backup", Lam "_" TUnit 
                            (App (Var "f")
                            (Record [
                                ("x", (Proj1(Record[("1", (Var "x"))]))),
                                ("backup", Proj1(Record [("1", (Var "x"))]))
                                ])
                            )
                        ),
                        ("reset", Lam "_" TUnit 
                            (App (Var "f")
                            (Record [
                                ("x", (Proj2(Record[("2", (Var "x"))]))),
                                ("backup", Proj2(Record [("2", (Var "x"))]))
                                ])
                            )
                        )
                    ])
                )
            )
        )
    )
    (Record [("x", nat 0), ("backup", nat 0)])

diverge :: Type -> Term 
diverge t = 
    Lam "_" TUnit 
        (Fix (Lam "x" t (Var "x")))

dType :: Type
dType = TRec "X" (TArrow (TVar "X") (TVar "X"))

lam :: Term
lam = Lam "f" (TArrow dType dType) 
        (Fold dType (Var "f"))

ap :: Term
ap = Lam "f" dType
       (Lam "a" dType 
         (App (Unfold (Var "f")) (Var "a")))

extendedDType :: Type 
extendedDType =  TRec "X" (TRecord[
    ("nat", TNat),
    ("fn", TArrow (TVar "X") (TVar "X")),
    ("bool", TAns)
    ])

natD :: Term -> Term
natD n = Fold extendedDType (Record [("nat", n)])

lamD :: Term -> Term
lamD f = Fold extendedDType (Record [("fn", f)])

truD :: Term
truD = Fold extendedDType (Record [("bool", Yes)])

flsD :: Term
flsD = Fold extendedDType (Record [("bool", No)])

apD :: Term
apD = Lam "f" extendedDType
      (Lam "a" extendedDType
        (App
          (App
            (Lam "fn" (TArrow extendedDType extendedDType)
              (App (Var "fn") (Var "a")))
            (Lam "nat" TNat
              (App (diverge extendedDType) Unit)))
          (Unfold (Var "f"))))

sucD :: Term
sucD = Lam "f" extendedDType 
        (App
            (App
                (Lam "nat" TNat
                    (Fold extendedDType (Record[("nat", Succ (Var "n"))])))
                (Lam "other" (TArrow extendedDType extendedDType)
                    (App (diverge extendedDType) Unit)))
            (Unfold (Var "f")))

zroD :: Term
zroD = Fold extendedDType (Record[("nat", Zero)])

ifElseDOld :: Term 
ifElseDOld = Lam "if" extendedDType
    (Lam "then" extendedDType
        (Lam "else" extendedDType
            (App
                (App
                    (Lam "bool" TAns
                        (If (Var "bool") (Var "then") (Var "else")))
                    (Lam "other" TUnit
                        (App (diverge extendedDType) Unit)))
                (Unfold (Var "if")))))

ifElseD :: Term
ifElseD = Lam "if" extendedDType
    (Lam "then" extendedDType
        (Lam "else" extendedDType
            (Case
                (Unfold (Var "if"))
                [
                    ("bool", "b", If (Var "b") (Var "then") (Var "else")),
                    ("nat", "n", App (diverge extendedDType) Unit),
                    ("fn", "f", App (diverge extendedDType) Unit)
                ]
            )
        )
    )

-- if false then 1 else 0 
ifFalse1 :: Term 
ifFalse1 = App
    (App
        (App ifElseD flsD)
        (Fold extendedDType (Record[("nat", nat 1)])))
    (Fold extendedDType (Record[("nat", Zero)]))
-- ghci> eval ifFalse1
-- Fold (TRec "X" (TRecord [("nat",TNat),("fn",TArrow (TVar "X") (TVar "X")),("bool",TAns)])) (Record [("nat",Zero)])

-- if false then 1 else false 
ifFalse2 :: Term 
ifFalse2 = App
    (App
        (App ifElseD flsD)
        (Fold extendedDType (Record[("nat", nat 1)])))
    (flsD)
-- ghci> eval ifFalse2
-- Fold (TRec "X" (TRecord [("nat",TNat),("fn",TArrow (TVar "X") (TVar "X")),("bool",TAns)])) (Record [("bool",No)])
