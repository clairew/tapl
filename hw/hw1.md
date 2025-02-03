## HW 1 

### TAPL 3.5.16 
Original semantics refer to figures 3-1, 3-2 in chapter 3. New semantics are from problem 3.5.16. Also to be consistent with implementation, `wrong` is represented as `TWrong` in code.  

### Formal Definition 

A term is stuck when it's not a value (not a boolean or numerical value) or no evaluation rule applies to it.

For any term t, t gets stuck in the original semantics if and only if t evaluates to wrong in the new semantics with `badnat` and `badbool`.

### Haskell Implementation 
```
data Term = 
    TTrue 
    | TFalse 
    | TIf Term Term Term 
    | TZero 
    | TSucc Term 
    | TPred Term 
    | TIsZero Term 
    | TWrong
    deriving (Show, Eq)

isNumericVal :: Term -> Bool
isNumericVal TZero = True
isNumericVal (TSucc t) = isNumericVal t
isNumericVal _ = False

isVal :: Term -> Bool 
isVal TTrue = True 
isVal TFalse = True 
isVal t | isNumericVal t = True 
isVal _ = False

isBadNat :: Term -> Bool
isBadNat TWrong = True
isBadNat TTrue = True
isBadNat TFalse = True
isBadNat _ = False 

isBadBool :: Term -> Bool 
isBadBool TWrong = True
isBadBool val = case isNumericVal val of 
    True -> True
    _ -> False
isBadBool _ = False
```

### Proof 

### 1. If t gets stuck in original semantics → t evaluates to wrong in new semantics.

#### Case TIf (by E-IF, E-IFTrue, E-IFFalse)
Implementation
```
# Original semantics
eval1Old :: Term -> Term
eval1Old (TIf TTrue t2 t3) = t2
eval1Old (TIf TFalse t2 t3) = t3
eval1Old (TIf t1 t2 t3) = case eval1Old t1 of
    t1' -> TIf t1' t2 t3
```

```
# New semantics
eval1 :: Term -> Term
eval1 (TIf TTrue t2 t3) = t2
eval1 (TIf TFalse t2 t3) = t3
eval1 (TIf t1 t2 t3)
    | isBadBool t1 = TWrong
    | otherwise = case eval1 t1 of 
    t1' -> (TIf t1' t2 t3)
    _ -> TWrong
```

#### Subcase - t1 evaluates to a non-boolean value.

Old semantics - Since t1 evaluates to a numeric value, there's no evaluation rule for TIf with a numeric guard (E-IFTRUE requires TTrue, E-IFFALSE requires TFalse, E-IF requires t1 to take a step), so it gets stuck.

New semantics - When t1 evaluates to a numeric value, which is a `badbool`. By rule E-IF-WRONG, if `badbool` → TWrong. Thus when t1 evaluates to a non-boolean, TIf t1 t2 t3 evaluates to TWrong. 

#### Subcase - t1 gets stuck during evaluation.

Old semantics - Suppose t1  →* t1' and t1' is stuck and not a boolean value, then for TIf t1' t2 t3, since t1' is stuck it can't take a step. E-IFTRUE, E-IFFALSE, and E-IF don't apply. Thus TIf t1' t2 t3 is stuck. 

New semantics - By induction hypothesis since t1 is a subterm of TIf t1 t2 t3, if t1 gets stuck in original semantics then t1 evaluates to TWrong in new semantics. TWrong is a `badbool` and by E-IF-WRONG, if `badbool` then t2 else t3 → TWrong. Thus when t1 gets stuck, TIf t1 t2 t3 evaluates to TWrong.

#### Cases TSucc, TPred, TIsZero (by E-SUCC, E-PREDZERO, E-PREDSUCC, E-PRED, E-ISZEROZERO, E-ISZEROSUCC, E-ISZERO)
Implementation 
```
# Old semantics
eval1Old (TSucc t1) = case eval1Old t1 of 
   t1' -> TSucc t1'
eval1Old (TPred TZero) = TZero
eval1Old (TPred (TSucc nv1)) | isNumericVal nv1 = nv1
eval1Old (TPred t1) = case eval1Old t1 of 
    t1' -> TPred t1'
eval1Old (TIsZero TZero) = TTrue
eval1Old (TIsZero (TSucc nv1)) | isNumericVal nv1 = TFalse
eval1Old (TIsZero t1) = case eval1Old t1 of 
    t1' -> TIsZero t1'
```
```
# New semantics
eval1 (TSucc t1)
    | isBadNat t1 = TWrong
    | isVal t1 = TSucc t1
    | otherwise = TSucc (eval1 t1) 
eval1 (TPred (TSucc nv1)) | isNumericVal nv1 = nv1
eval1 (TPred TZero) = TZero
eval1 (TPred t1)
    | isBadNat t1 = TWrong
    | otherwise = case eval1 t1 of
    TZero -> TZero
    t1' -> TPred t1'
    _ -> TWrong
eval1 (TIsZero TZero) = TTrue
eval1 (TIsZero (TSucc nv1)) | isNumericVal nv1 = TFalse
eval1 (TIsZero t1)
    | isBadNat t1 = TWrong
    | otherwise = case eval1 t1 of 
    t1' -> TIsZero t1'
    _ -> TWrong 
```

For each of these terms that expect numeric input:

#### Subcase - t1 evaluates to a boolean value
Old semantics - since t1 evaluates to a boolean value, there's no evaluation rule for these operations on a boolean, so they get stuck.

New semantics - When t1 evaluates to a boolean value, isBadNat evaluates t1 as a `badnat`, which returns TWrong. By the respective E-*-WRONG rule, the operation on `badnat` → TWrong.

#### Subcase - t1 gets stuck during evaluation
Old semantics - since t1 is stuck, no rule applies to these operations.

New semantics - By induction hypothesis, if t1 gets stuck in original semantics then t1 evaluates to TWrong in new semantics. TWrong is a `badnat` and by the respective E-*-WRONG rule, the operation evaluates to TWrong.
 

### 2. If t evaluates to wrong in new semantics → t would have been stuck in original semantics.

#### Case TIf (by E-IF-WRONG)
#### Subcase - t1 evaluates to a non-boolean value.
In original semantics, there is no rule for TIf with a numeric value, thus it gets stuck. 
#### Subcase - t1 evaluates to wrong.
By induction, t1 would be stuck in original semanatics. Thus TIf t1 t2 t3 would be stuck. 

#### Cases TSucc, TPred, TIsZero (by E-SUCC-WRONG, E-PRED-WRONG, E-ISZERO-WRONG)
For each of these terms, if they evaluate to wrong, then t1 must be badnat, which happens in two cases:
#### Subcase - t1 evaluates to a boolean value
In original semantics, there is no rule for these operations with a boolean value, thus they get stuck.
#### Subcase - t1 evaluates to wrong
By induction, t1 would be stuck in original semantics. Thus the entire term would be stuck (since each operation requires t1 to evaluate).

### 3.5.17 - still a draft/WIP..
### Formal Definition 
For any term t and value v, t evaluates to v in small steps (→) if and only if t evaluates to v in big step (⇓)

Implementation 
```
# small step evaluation 
eval1 :: Term -> Term
eval1 (TIf TTrue t2 t3) = t2
eval1 (TIf TFalse t2 t3) = t3
eval1 (TIf t1 t2 t3)
    | isBadBool t1 = TWrong
    | otherwise = case eval1 t1 of 
    t1' -> TIf t1' t2 t3
    _ -> TWrong
eval1 (TSucc t1)
    | isBadNat t1 = TWrong
    | isVal t1 = TSucc t1
    | otherwise = TSucc (eval1 t1) 
eval1 (TPred (TSucc nv1)) | isNumericVal nv1 = nv1
eval1 (TPred TZero) = TZero
eval1 (TPred t1)
    | isBadNat t1 = TWrong
    | otherwise = case eval1 t1 of
    TZero -> TZero
    t1' -> TPred t1'
    _ -> TWrong
eval1 (TIsZero TZero) = TTrue
eval1 (TIsZero (TSucc nv1)) | isNumericVal nv1 = TFalse
eval1 (TIsZero t1)
    | isBadNat t1 = TWrong
    | otherwise = case eval1 t1 of 
    t1' -> TIsZero t1'
    _ -> TWrong 
eval1 _ = TWrong

# big step evaluation 
eval2 (TIf t1 t2 t3) = case (eval2 t1, eval2 t2, eval2 t3) of 
    (TTrue, t2', _) -> t2'
    (TFalse, _, t3') -> t3'
    _ -> TWrong 

eval2 (TPred t1) = case (eval2 t1) of 
    (TZero) -> TZero
    ((TSucc t1)) -> t1 
    (t1') -> (TPred t1')
    _ -> TWrong 

eval2 (TIsZero t1) = case (eval2 t1) of 
    (TZero) -> TTrue
    ((TSucc t1)) -> TFalse 
    (t1') -> (TIsZero t1') 
    _ -> TWrong 

# using perform all single steps needed to reach final value 
evalMulti :: Term -> Term
evalMulti t 
    | isVal t = t
    | t == TWrong = TWrong
    | otherwise = evalMulti (eval1 t)
```

### Proof

#### If a term τ can reach value v through any number of small evaluation steps, then it must also evaluate to the same value v when evaluated in one big step.

#### Induction hypothesis - For any subterm t', if t' -> * v' then t' ⇓ v'. 

Base case - If  t = v  is already a value, then by the (B-Value) rule in big-step semantics: v ⇓ v

Inductive cases 
#### Case TIf
#### Subcase - t1 then t2 else t3 → t2 if t1 →* true
Assume t1 →* true, then by IH, t1 ⇓ true. Assume t2 →* true, then by IH, t2 ⇓ true. Using B-IfTrue rule, if t1 then t2 else t3 ⇓ v2.
#### Subcase - t1 then t2 else t3 → t3 if t1 →* false 
Assume t1 ->* false, then by IH, t1 ⇓ false. Assume t3 ->* v3, then by IH, t3 ⇓ true. By B-IfFalse rule, if t1 then t2 else t3 ⇓ v3. 

#### Case Succ t1
Assume t1 ->* nv1. By IH, t1 ⇓ nv1. Using B-Succ rule, succ t1 ⇓ succ nv1.

#### Case Pred t1 
#### Subcase - pred t1 → 0 if t1 →* 0
Assume t1 →* TZero. By IH for t1, we have t1 ⇓ 0. Apply the B-PredZero rule to conclude pred t1 ⇓ 0.

#### Subcase - pred t1 → nv1 if t1 →* succ nv1
Assume t1 →* succ nv1 . By IH, t1 ⇓ succ nv1. Applying the B-PredSucc rule, pred t1 ⇓ nv1.

#### Case IsZero t1 
#### Subcase - t1 → true if t1 →* TZero
Assume t1 →* 0, by IH, we have t1 ⇓ 0. Using B-IsZero rule, iszero t1 ⇓ true.. 
#### Subcase -  t1 → false if t1 →* succ nv1:
Assume t1 →* succ nv1. By IH, t1 ⇓ succ nv1.. Apply the B-IszeroSucc rule -  iszero t1 ⇓ false. 

#### If a term τ evaluates to a value v in one big step, then it must also be able to reach that value v through some number of small evaluation steps. 

#### Induction hypothesis - For any subterm t', if t' ⇓ v' then t' -> * v'.  

Base case - a value v small-step evaluates to itself in zero or more steps.

Inductive cases 
#### Case TIf 
#### Subcase -  if t1 then t2 else t3 ⇓v2, when t1 ⇓ true and t2 ⇓ v2
By IH for t1, t1 ->* true. By IH for t2, t2 ->* v2. Using small-steps, t1 then t2 else t3 →* true then t2 else t3 (by t1 →* true) → t2 (by the rule for E-IfTrue) →* v2 (by t2 →* v2). 
#### Subcase - if t1 then t2 else t3 ⇓v3, when t1 ⇓ false and t3 ⇓ v3
By IH for t1, t1 ->* false. By IH for t3, t3 ->* v3. Using small-steps, t1 then t2 else t3 →* false then t2 else t3 (by t1 →* false) → t3 (by the rule for E-IfFalse) →* v2 (by t3 →* v3). 
#### Succ t1 
For the rule B-Succ to apply, it must be the case that t1 ⇓ nv1. By IH since t1 ⇓ nv1, t1 →* nv1. Using E-SUCC, if t1 is a numeric value nv1, then succ t1 reduces to succ nv1 in a single step. Succ t1 reduces to succ nv1 in small-step. 
#### Pred t1
#### Subcase - pred t1 ⇓ 0 if t1 ⇓ 0
By IH since t1 ⇓ 0, we have t1 →* 0. Using E-PREDZERO, if t1 →* 0, then pred t1 → 0.
#### Subcase - pred t1 ⇓ nv1 if t1 ⇓ succ nv1
By IH for t1, since t1 ⇓ succ nv1, t1 →* succ nv1. Using E-PREDSUCC if t1 →* succ nv1, then pred t1 → nv1. 
#### IsZero t1 
#### Subcase - IsZero t1 ⇓ true if t1 ⇓ 0
By IH for t1, since t1 ⇓ 0, t1 →* 0. Using E-IsZeroZero, if t1 →* 0, then iszero t1 → true. 

#### Subcase - IsZero t1 ⇓ false if t1 ⇓ succ nv1
By IH for t1, since t1 ⇓ succ nv1, t1 →* succ nv1. Using E-IsZeroSucc, if t1 →* succ nv1, then iszero t1 → false. 