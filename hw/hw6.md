## HW 6

Note - before all of this code, I used my System F implementation. So - still need [all of that](../src/SystemF.hs) STLC with polymorphism typing and evaluation baloney. 

### 22.3.9, 22.3.10

```
data UVarGen = NextUVar String UVarGen

initialUVarGen :: UVarGen
initialUVarGen = go 0
    where go n = NextUVar ("?X_" ++ show n) (go (n+1))

freshGenVar :: UVarGen -> (Type, UVarGen)
freshGenVar (NextUVar name nextGen) = (TVar name, nextGen)

inferConstraints :: Context -> Term -> UVarGen -> (Type, ConstraintSet, UVarGen)
inferConstraints ctx Zero freshVarGen = (TNat, [], freshVarGen)
inferConstraints ctx TTrue freshVarGen = (TBool, [], freshVarGen)
inferConstraints ctx TFalse freshVarGen = (TBool, [], freshVarGen)
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
```

Above is code for the fresh variable generator, and using constraint generation (`inferConstraints`) with the generator.

`inferConstraints` accepts a typing context, a term, and a fresh variable generator, and returns a type, set of constraints, and a fresh variable generator with the remaining unused fresh variables from the input fresh variable generator. 

#### Prove that the constraint generation rules with the fresh variable generator are equivalent to the original constraint generation rules. 

Proving the equivalence can be broken down to soundness and completeness. 

#### Soundness - If  $\Gamma$ ⊢F t:T |F' C, and variables in $\Gamma$ and t do not appear in F, then $\Gamma$ ⊢F t:T |F\F' C 

Induction on typing derivations.

Base cases:
- Constants and Var - a newly initiated F is returned, where F contains variables that aren't in the typing context or the term. The implementation with the fresh variable generator returns an empty constraint sets, the constant's type (or for Var, looks up variable's type), and the newly initiated fresh variable generator - which is the same as the original system.  

Inductive cases:
- Lambda - By IH the subsequent calls that pass the initial fresh variable generator will not contain variables that aren't in the typing context or term. Variable generator is then passed on to subsequent calls. 
- App - By IH, the subsequent calls that pass the initial fresh variable generator will not contain variables that aren't in the typing context or term. The head of the fresh variable generator is used for the new constraint, and the subsequence sequence of the fresh variable generator is passed onto subsequent calls.

### 22.4.6
```
type Substitution = Map.Map String Type

emptySubst :: Substitution
emptySubst = Map.empty

singleSubst :: String -> Type -> Substitution
singleSubst x t = Map.insert x t emptySubst

applySubst :: Substitution -> Type -> Type
applySubst subst ty =
    Map.foldrWithKey (\var replacement result ->  
                       substType var replacement result)
                     ty
                     subst

composeSubst :: Substitution -> Substitution -> Substitution
composeSubst s1 s2 =
    let s2Applied = Map.map (applySubst s1) s2
    in Map.union s2Applied s1

unify :: Type -> Type -> Maybe Substitution
unify t1 t2 = unifyConstraints [(t1, t2)]

unifyConstraints :: ConstraintSet -> Maybe Substitution
unifyConstraints [] = Just emptySubst
unifyConstraints ((t1, t2):rest)
    | t1 == t2 = unifyConstraints rest
    | TVar v <- t1, not (v `Set.member` freeTypeVars t2) =
        let subst = singleSubst v t2
            rest' = map (\(a, b) -> (applySubst subst a, applySubst subst b)) rest  
        in do
            result <- unifyConstraints rest'
            return (composeSubst result subst)
    | TVar v <- t2, not (v `Set.member` freeTypeVars t1) =
        let subst = singleSubst v t1
            rest' = map (\(a, b) -> (applySubst subst a, applySubst subst b)) rest 
        in do
            result <- unifyConstraints rest'
            return (composeSubst result subst)
    | TArrow s1 s2 <- t1, TArrow t1' t2' <- t2 =
        let newConstraints = [(s1, t1'), (s2,t2')]
        in unifyConstraints (newConstraints ++ rest)
    | otherwise = Nothing
```

### 22.5.5
```
inferPrincipalType :: Context -> Term -> Maybe Type
inferPrincipalType ctx t1 =
    let (inferredType, constraints, _) = inferConstraints ctx t1 initialUVarGen
    in do
        subst <- unifyConstraints constraints
        return (applySubst subst inferredType)
```
