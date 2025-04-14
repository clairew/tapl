## HW 8 

### 20.1.2
```
-- We'll need TRec and define Fold, Unfold, and Fix as terms. 
data Type = TRec String Type
data Term = Fold Type Term | Unfold Term | Fix Term

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

subst x s (Fold typ t) = Fold typ (subst x s t)
subst x s (Unfold t) = Unfold (subst x s t)
subst x s (Fix t) = Fix (subst x s t)

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


streamType :: Type
streamType = TRec "A" (TArrow TUnit (TProd TNat (TVar "A")))

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
```

### 20.1.3
```
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

```

### 20.1.4
```

diverge :: Type -> Term 
diverge t = 
    Lam "_" TUnit 
        (Fix (Lam "x" t (Var "x")))

extendedDType :: Type 
extendedDType =  TRec "X" (TRecord[
    ("nat", TNat),
    ("fn", TArrow (TVar "X") (TVar "X")),
    ("bool", TAns)
    ])

ifElseD :: Term 
ifElseD = Lam "if" extendedDType
    (Lam "then" extendedDType
        (Lam "else" extendedDType
            (App
                (App
                    (Lam "bool" TAns
                        (If (Var "bool") (Var "then") (Var "else")))
                    (Lam "other" TUnit
                        (App (diverge extendedDType) Unit)))
                (Unfold (Var "if")))))

flsD :: Term
flsD = Fold extendedDType (Record [("bool", No)])

-- if false then 1 else 0 
ifFalse1 :: Term 
ifFalse1 = App
    (App
        (App ifElseD flsD)
        (Fold extendedDType (Record[("nat", nat 1)])))
    (Fold extendedDType (Record[("nat", Zero)]))

-- if false then 1 else false 
ifFalse2 :: Term 
ifFalse2 = App
    (App
        (App ifElseD flsD)
        (Fold extendedDType (Record[("nat", nat 1)])))
    (flsD)

```

### 21.5.2 
- $S_f$ and $S$ are invertible.
    - Case 1: {${(T,Top) | T \in T_f}$} - Since case 1 doesn't rely on $R$, the generating set is $\emptyset$. 
    - Case 2: {$(S_1 X S_2, T_1 X T_2) | (S_1, T_1), (S_2,T_2) \in R$}. The generating minimal set is {$(S_1, T_1), (S_2, T_2)$}. 
    - Case 3: {$(S_1 \rightarrow S_2, T_1 \rightarrow T_2) | (T_1,S_1), (S_2,T_2) \in R$}. The generating minimal set is {$(T_1,S_1),(S_2,T_2)$}