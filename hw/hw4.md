## HW 4

### 15.3.6 
#### If $v$ is a closed value of type $T_1 \rightarrow T_2$ then $v$ has the form  $\lambda x:S_1.t_2$.

Closed value of type $T_1 \rightarrow T_2$ is in the form of $\lambda x:S_1.t_2\ $ by T-Abs or T-Sub. T-Abs is used for the function arrow type, and has the form $\lambda x:S_1.t_2\text{.}$ 

With T-Sub, we have $v:S$ where $S<:T_1 \rightarrow T_2$. Using the inversion lemma, $S = S_1 \rightarrow S_2$ for some $S_1, S_2$, we get $v: S_1 \rightarrow S_2$. By IH on the smaller derivation, $v$ has the form $\lambda x:S_1.t_2$.

#### If $v$ is a closed value of type $\{ l_i:T_i^{i \in 1..n}\}$, then $v$ has the form $\{ k_j:v_j^{a \in 1..m}\}$ with $\{l_i^{i \in 1..n}\} \subseteq \{k_j^{a \in 1..m}\}$. 

If $v$ is a closed value of type $\{ l_i:T_i^{i \in 1..n}\}$, then by the inversion lemma on record types, $v$ must have the form $\{ k_j:v_j^{a \in 1..m}\}$ where $\{l_i^{i \in 1..n}\} \subseteq \{k_j^{a \in 1..m}\}$.   

### 16.1.3
Haskell implementation for algorithmic subtyping, which includes the `TBool` case:
```
 subtype :: Type -> Type -> Bool
 subtype s t = case (s, t) of
     (TNat, TNat) -> True
     (TAns, TAns) -> True
     (TBool, TBool) -> True
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

```

Lemma from 16.1.2 still holds, when TBool is explicitly handled. 

### 16.2.5
By induction:

- T-Var - By TA-Var.
- T-Abs  $\lambda x:T_1.t_2$
    - By IH on $t_2$, there exists some $s_2$ where $x:T_1 ⊢ t_1 : S_2$ where $s_2 <: t_2$ 
    - Using T-Abs $Γ ⊢ \lambda x:T_1.t_1 : T_1→S_2$, 
    - By S-Arrow, If $T_1 <: T_1$ and $S_2 <: T_2$ then $T_1→S_2 <: T_1\rightarrow T_2$. 
- T-App $Γ ⊢ t_1 : T_{11}→T_{12}$ $Γ ⊢ t_2 : T_{11}$ 
    - By IH on $t_1$ - we have some $S_1$ where $Γ ⊢ t_1 : S_1$ and $S_1 <: T_{11}→T_{12}$. 
    - By inversion of subtyping, $S_1 is a function type. 
    - $S_1$ must be of form $S_{11}→S_{12}$ where $T_{11} <: S_{11}$ and $S_{12} <: T_{12}$.
    - By IH on $t_2$, we get some $S_2$ where $Γ ⊢ t_2 : S_2$ and $S_2 <: T_{11}$. 
    - Since $S_2 <: T_{11}$ and $T_{11} <: S_{11}$, $S_2 <: S_{11}$.
    - $Γ ⊢ t_1 : S_{11}→S_{12}$ and $Γ ⊢ t_2 : S_2$ and $ S_2 <: S_{11}$, so $Γ ⊢ t_1 t_2 : S_{12}$.  
- T-Rcd
    - By IH For each $t_i$, we get $Γ ⊢ t_i : S_i$ and $ S_i <: T_i$.
    - Using T-Sub for each $t_i$, $Γ ⊢ ti : Ti$. 
- T-Proj
    - By IH on $t_1$, $Γ ⊢ t_1 : S_1$, $S <: \{l_i:T_i ^{i∈1}\}..n$
    - By inversion on subtyping on records, $S_1$ must have the form $\{l_i:T_i ^{i∈1}\}..m$ where $m >= n$. For eaach i in 1..n, $S_i <= T_i$. 
    - By TA-Proj, $⊢t_1.l_j : Sj$. Since $S_j ≤ T_j$, we have our minimal type. 
- T-Sub 
    - By IH there is some minimal type M where $⊢t : M$ and $M ≤ S$. 
    - By transitivity, since $M ≤ S$ and $S ≤ T$, $M ≤ T$. 
### 16.2.6
```
subtype :: Type -> Type -> Bool
subtype s t = case (s, t) of
    (TNat, TNat) -> True
    (TArrow s1 s2, TArrow t1 t2) -> subtype t1 s1 && subtype s2 t2 
    (_, TTop) -> True
    _ -> False
```
Without the `TArrow` case, we wouldn't be able to evaluate to the base case for `TNat`. 

### 16.3.2 
Prove: 
1. For every pair of types $S$ and $T$, there is some type $J$ such that $S \lor T = J$. 
2. For every pair of types S and T with a common subtype, there is some type
$M$ such that $S \land T= M$.

Due to the TArrow case, meet and join must be calculated mutually recursively. Below are the mutually recursive algorithms used:

```
join :: Type -> Type -> Maybe Type
join TBool TBool = TBool
join (TArrow s1 s2) (TArrow t1 t2) = 
  TArrow (meet s1 t1) (join s2 t2)  -- M₁ = S₁ ∧ T₁ and J₂ = S₂ ∨ T₂
join (TRecord sFields) (TRecord tFields) = 
  TRecord $ [ (l, join s t) 
          | (l, s) <- sFields
          , (l', t) <- tFields
          , l == l'  -- take only fields in both records; intersection
          ]
join _ _ = TTop

meet :: Type -> Type -> Maybe Type
meet s TTop = s
meet TTop t = t
meet TBool TBool = TBool
meet (TArrow s1 s2) (TArrow t1 t2) = 
  TArrow (join s1 t1) (meet s2 t2)  -- J₁ = S₁ ∨ T₁ and M₂ = S₂ ∧ T₂
meet (TRecord sFields) (TRecord tFields) = 
  Record $ unionFields
  where
    allFields = nub $ map fst sFields ++ map fst tFields
    unionFields = [ (l, fieldType l) | l <- allFields ]
    fieldType l = case (lookup l sFields, lookup l tFields) of
      (Just s, Just t) -> meet s t    -- field in both records
      (Just s, Nothing) -> s          -- field only in S
      (Nothing, Just t) -> t          -- field only in T
      (Nothing, Nothing) -> Nothing
meet _ _ = Nothing
```

Since both return `Maybe Type`, we need to prove totality to show when there's a common subtype, it gets returned. 

#### Join ($S \lor T = J$) 

By structural induction: 
- Base cases 
    - If both types are TBool -> returns TBool 
    - If either type is TTop -> returns TTop. 
- Inductive cases
    -  (TArrow s1 s2) ∨ (TArrow t1 t2)
        - join s2 t2 by IH. If `meet s1 t1` fails, then `join _ _` results to TTop. Thus always returns a result. 
    - (TRecord sFields) (TRecord tFields) 
        - By IH each field join exists. Result is a record with subset of fields, thus always returns a result. 


#### Meet ($S \land T= M$)

By structural induction:
- Base cases
    - If either is TTop -> returns the other type
    - If either is TBool -> returns TBool. 
- Inductive cases 
    - (TArrow s1 s2) ∧ (TArrow t1 t2)
        - If there exists some type L that is a subtype of both S and T, by inversion lemma L must also be an arrow type $L_1 \rightarrow L_2$ where $s1 \subseteq L1$ and $t1 \subseteq L1$, and $L2 \subseteq s2$ and $L2 \subseteq t2$. 
    - (TRecord sFields) (TRecord tFields)
        - If some type L is a common subtype of S and T, then by the record subtyping rule it must have at least all the fields that appear in either S or T. If a field appears in both S (type s) and T (type t) - then L's type for the field is a subtype of both s and t, thus s and t have a common subtype, thus succeeding by induction. If a field x of L only appears in S, since L is a subtype of S, L must have field x by inversion lemma. The field x in L must be a subtype of S's field x of type s. Thus for unique fields, the original type is kept.  

Now we need to prove that Join is an upper bound, and Meet is a lower bound. 
By induction:

#### Join is an upper bound

- Base cases:
    - If S: TBool, T: TBool, then J: TBool and  $TBool\subseteq TBool$
    - If either type has no common structure, J: TTop and $S\subseteq TTop, T\subseteq TTop$
- Inductive cases:
    - Case $S: S_1 \rightarrow S_2, T: T_1 \rightarrow T_2$:
    Let $M_1: S_1\land T_1 \text{and} J_2: S_2 \land T_2$. 
        - $J: M₁\rightarrow J₂$
        - By IH: $S_2 \subseteq J_2$ and $T_2 \subseteq J_2$
        - By S-Arrow rule: if $M_1 \subseteq S_2$ and $S_2 \subseteq J_2$ then $S_1 \rightarrow S_2 \subseteq M_1 \rightarrow J_2$
        - Therefore $S\subseteq J$ (similarly for $T \subseteq J$). 

    - Case S and T are records:
        - J contains intersection of fields
        - For each common field $l: S.l\lor T.l: J.l$
        - By IH: $S.l \subseteq J.l$ and $T.l\subseteq J.l$
        - By S-Record: $S\subseteq J$ and $T\subseteq J$

#### Meet is a lower bound 
- Base cases:
    - If S: TTop, then $M \subseteq T$ and $T \subseteq TTop$
    - If T: TTop, then $M \subseteq S$ and $S \subseteq TTop$
    - If S: TBool, T: TBool, then M: TBool and $TBool \subseteq TBool$

- Inductive cases:
    - Case $S: S_1\rightarrow S_2$, $T: T_1\rightarrow T_2$:
        - Let $J_1 = S_1\lor T_1$ and $M_2 = S_2\land T_2$ 
        - $ M: J_1 \rightarrow M_2$
        - By IH: $M_2\subseteq S_2$ and $M_2\subseteq T_2$
        - By S-Arrow: if $S_1\subseteq J_1$ and $M_2\subseteq S_2$ then $J_1\rightarrow M_2\subseteq S_1\rightarrow S_2$
        - Therefore $M\subseteq S (M\subseteq T)$

    - Case S and T are records:
        - M contains union of fields
        - For common fields: $M.l \subseteq S.l\land T.l$
        - For fields only in $S: M.l \subseteq S.l$
        - For fields only in $T: M.l \subseteq T.l$
        - By IH and construction: $M\subseteq S$ and $M\subseteq T$

Finally, we prove the optimality of upper bound and lower bound. 

#### Join is is the least upper bound if $S \subseteq U$ and $T \subseteq U$, then $J \subseteq U$ where $S \lor T = J$. 

Proof by cases on the type of U:

- U: TTop
    - $J \subseteq TTop$ for any $J$
- U: TBool 
    - By inversion lemma, S and T must be of type TBool. Thus J: TBool and $TBool \subseteq TBool$. 
- U: $U_1 \rightarrow U_2$ 
    - By inversion lemma, $S: S_1\rightarrow S_2$, $T: T_1\rightarrow T_2$
    - $J: M_1\rightarrow J_2$ where $M_1 = S_1\land T_1$, $J_2 = S_2\lor T_2$
    - By IH: $U_1\subseteq M_1$ and $J_2\subseteq U_2$. 
    - By S-Arrow: $J\subseteq U$
- U: TRecord 
    - By inversion lemma, S and T must be records
    - J contains intersection of fields
    - For each field l in U: by IH, $J.l\subseteq U.l$
    - By S-Record: $J\subseteq U$

#### Meet is the greatest lower bound if $L \subseteq S$ and $L \subseteq T$, then $L \subseteq M$ where $S \land T = M$. 

Proof by cases on type of S and T:
- Either is type TTop
    - M is the other type.
- $S: TBool$, $T: TBool$
    - M: TBool, by inversion lemma L: TBool. 
- $S: S_1 \rightarrow S_2$, $T: T_1 \rightarrow T_2$ 
    - By inversion lemma, $L: L_1\rightarrow L_2$ where $S_1\subseteq L_1, T_1\subseteq L_1, L_2\subseteq S_2, L_2\subseteq T_2$
    - M: $J_1\rightarrow M_2$ where $J_1 = S_1\lor T_1, M_2 = S_2\land T_2$
    - By IH: $L_1\subseteq J_1$ and $L_2\subseteq M_2$
    - By S-Arrow: $L\subseteq M$
- $S: TRecord$, $T: TRecord$
    - By inversion lemma, L: TRecord
    - L must have all fields from S and T
    - For common fields: by IH, $L.l\subseteq M.l$
    - For unique fields: $L.l\subseteq S.l$ or $L.l\subseteq T.l$ 
    - By S-Record: $L\subseteq M$