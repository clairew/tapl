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
data Term = Case Term [(String, String, Term)]
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
freeVars (Case t branches) = 
    Set.union 
        (freeVars t)
        (Set.unions [Set.delete var (freeVars branch) | (tag, var, branch) <- branches])
subst x s (Case t branches) =
    Case (subst x s t)
        [(tag, var, if x == var 
                    then branch 
                    else if Set.member var (freeVars s)
                         then let fresh = freshVar var (freeVars s)
                              in subst x s (subst var (Var fresh) branch)
                         else subst x s branch) 
         | (tag, var, branch) <- branches]
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

Also had to add a Case term to check and extract the Record fields. 

Results of evaluating ifFalse1 and ifFalse2
```
ghci> eval ifFalse1
Fold (TRec "X" (TRecord [("nat",TNat),("fn",TArrow (TVar "X") (TVar "X")),("bool",TAns)])) (Record [("nat",Zero)]) 
-- Returns <nat=0>

ghci> eval ifFalse2
Fold (TRec "X" (TRecord [("nat",TNat),("fn",TArrow (TVar "X") (TVar "X")),("bool",TAns)])) (Record [("bool",No)])
-- Returns <bool=false>. In my TypedLC, Yes represents True and No, False. 
```

### 21.5.2 
- $S_f$ and $S$ are invertible. Invertibility depends on the structure of the generating form, not the domain. $S_f$ and $S$ have identical rule structures. 
    - Case 1: {${(T,Top) | T \in T_f}$} - Since case 1 doesn't rely on $R$, the generating set is $\emptyset$. 
    - Case 2: {$(S_1 X S_2, T_1 X T_2) | (S_1, T_1), (S_2,T_2) \in R$}. The generating minimal set is {$(S_1, T_1), (S_2, T_2)$}. 
    - Case 3: {$(S_1 \rightarrow S_2, T_1 \rightarrow T_2) | (T_1,S_1), (S_2,T_2) \in R$}. The generating minimal set is {$(T_1,S_1),(S_2,T_2)$}
- Support functions for $S_f$ and $S$. They are identifical because the structure of the generating functions are the same, and have the same 3 clauses. 
    - support $S_f (S,T) =$
        - $\emptyset$ if $(S,T)$ is of the form $(T,Top)$
        - {$(S_1, T_1), (S_2, T_2)$} if $(S,T)$ is of the form $(S_1 X S_2, T_1 X T_2)$
        - {$(T_1,S_1),(S_2,T_2)$} if $(S,T)$ is of the form $(S_1 \rightarrow S_2, T_1 \rightarrow T_2)$ 
        - $\uparrow$ otherwise 

### 21.5.6
No because the generating function could be an infinite sequence - for example, a generator function that continues to increment the result in the previous call in the current call, and passes that to the next call, and so on. 

### 21.5.13 
#### Prove - If $lfp_F(X)$ = true, then $X \subseteq \mu F$
For $lfp_F(X)$ = true, either $X=\emptyset$ or $lfp(support(X))$= true. When $X = \emptyset$, $X \subseteq \mu F$. If $lfp(support(X))$ = true, then by IH, $support(X) \subseteq \mu F$, and by lemma 21.5.8, $X \subseteq \mu F$. 

#### Prove - If $lfp_F(X)$ = false, then $X \not\subseteq \mu F$. 
For $lfp_F(X)$ = false, either $support(X) \uparrow$ or $lfp(support(X)) \uparrow$. By lemma 21.5.8, since $support(X) \uparrow$, $X \not\subseteq \mu F$. If $lfp(support(X))$ = false, and by IH $support(X) \not\subseteq \mu F$, then by lemma 21.5.8  $X \not\subseteq \mu F$.

What would prevent $lfp_F$ from terminating is if $support(X)$ doesn't reduce $X$ or $support(X) \downarrow$. 

A class of generating function where $lfp_F$ would terminate could be size-reducing generating functions - for any non-empty set $X$, $|support(X)| < |X|$, and support($\emptyset$) = $\emptyset$. Each recursive support call reduces $X$, and after at most $|X|$ steps, we reach the empty set. When we reach $\emptyset$, $lfp_F$ terminates. 