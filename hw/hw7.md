## HW 7

### 26.3.5 

```
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
```

### 26.4.11
```
data Type
    = TVar String
    | TArrow Type Type
    | TForall String Type Type
    | TUnit
    | TNat
    | TAns
    | TBool
    | TTop
    deriving (Show, Eq)

data Context = Context
    { termVars :: [(String, Type)]
    , typeVars :: [(String, Type)] -- String is the var name and Type is its bound  
    } deriving (Show, Eq)

extendTypeVar :: String -> Type -> Context -> Context
extendTypeVar a bound (Context terms types) = Context terms ((a,bound):types) 

lookupTypeVar :: String -> Context -> Maybe Type 
lookupTypeVar a (Context _ types) = lookup a types

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
isSubtype _ _ _ = False

isWellFormedType :: Context -> Type -> Bool
isWellFormedType ctx (TVar v) = typeVarInContext v ctx
isWellFormedType ctx (TArrow t1 t2) = isWellFormedType ctx t1 && isWellFormedType ctx t2
isWellFormedType ctx (TForall v bound t) =
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
```
Prove:
- If $\Gamma \vdash S_1 \rightarrow S_2 <: T$ then either $T = TTop$ or else $T = T_1 \rightarrow T_2$ with $\Gamma \vdash T_1 <: S_1 $ and $\Gamma \vdash S_2 <: T_2 $.
  - S-TOP - already the case since $TTop$ is the maximum type. 
      - S-REFL - already the case. 
      - S-TVar - Doesn't apply. 
      - S-ALL - Doesn't apply. 
      - S-Arrow - Since we are already addressing the final form of $\Gamma \vdash S_1 \rightarrow S_2 <: T_1 \rightarrow T_2$, and S-Arrow's final form is deduced from the conditions that $\Gamma \vdash T_1 <: S_1$ and $\Gamma \vdash S_2 <: T_2$, which is already one of the types that $T$ can be. 
      - S-TRANS - By IH: U is either $TTop$ or $U_1 \rightarrow U_2$ with $U_1 <: S_1, U_2 <: U_2$.
          - $U = TTop$: only supertype of $TTop$ is $TTop$, so $T$ must be $TTop$.
          - $U = U_1 \rightarrow U_2$. By IH, $U_1 \rightarrow U_2$ is either $TTop$ (covered by the former case) or $T_1 \rightarrow T_2$ with $\Gamma \vdash T_1 <: U_1 $ and $\Gamma \vdash U_2 <: T_2 $. Then by transitive property, $T_1 <: S_1$ and $S_2 <: T_2$, thus by S-Arrow $\Gamma \vdash S_1 \rightarrow S_2 <: T_1 \rightarrow T_2$
-  If $\Gamma \vdash \forall X <: U.S_2 <: T$, then either $T = TTop$ or $T = \forall X <: U.T_2$ with $\Gamma, X <: U \vdash S_2 <: T_2$. 
    - S-TOP - Already the case. 
    - S-REFL - Already the case.
    - S-TVar - Doesn't apply.
    - S-Arrow - Doesn't apply. 
    - S-ALL - If the last rule applied was S-ALL, then the resulting form would be $\Gamma \vdash \forall X <: U.S_2 <: T$, which the premise already has.  
    - S-TRANS -  By IH: U is either $TTop$ or $\forall X <: U.T_2$ with $\Gamma, X <: U \vdash S_2 <: T_2$. 
      - U = $TTop$ - supertype of $TTop$ is $TTop$ - so $T = TTop$.
      - U =  $\forall X <: U.V_2$ <: T with $\Gamma, X <: U \vdash S_2 <: V_2$. 
        - S-TOP: T = TTop 
        - S-REFL: T = $\forall X <: U.V_2$
        - S-ALL: T = $\forall X <: U.V_2$, applying S-ALL gets $\forall X <: U.S_2 <: \forall X <: U.V_2$, thus T = $\forall X <: U.V_2$.  
- If $\Gamma \vdash X <: T$ then either $T = TTop$ or $T = X$ or $\Gamma \vdash S <: T$ with $X <: S \in \Gamma$. 
    - S-TOP: Maximum type, already the case. 
    - S-REFL - In the case of $T = X$. 
    - S-TVar - By IH, since $S <: T$ with $X <: S \in \Gamma$, by S-Trans $X <: T$ giving us the form in the premise. 
    - S-Arrow and S-All don't apply. 
    - S-TRANS - By IH U is either $TTOP$, $X$, or $\Gamma \vdash S <: U$ with $X <: S \in \Gamma$. 
      - U = $TTOP$: $S<: U, \Gamma \vdash TTOP <: T$. By S-REFL, $T$ would be $TTOP$.$S<:TTOP$ and $TTOP$ is the maximal type. 
      - U = $X$: $S <: X, X <: T$. $X <: T$ is already in the premise, by IH one of the 3 conditions must hold on this smaller derivation. 
      - $\Gamma \vdash S <: U$ with $X <: S \in \Gamma$: With the 2nd premise of S-TRANS $U<:T$, use transitivity with $S<:U, U<:T$ to get $S<:T$.
- If $\Gamma \vdash TTop <: T$ then $T = TTOP$  
  - S-TOP: Doesn't apply.
  - S-REFL: Already the case.
  - S-TVar: Doesn't apply.
  - S-ARROW: Doesn't apply.
  - S-ALL: Doesn't apply. 
  - S-TRANS: Let $S = TTop, U = TTop, T = TTop$, by S-REFL and IH, $S <: U, U<: T, S<:T$.
  
### 28.2.3

### 28.7.1 
