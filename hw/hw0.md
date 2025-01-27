## HW 0
Write out the formal definition of substitution on deBruijn-indexed terms.

## 1. Mathematical Definition

Let $[j \mapsto s]t$ denote the substitution of term $s$ for variable number $j$ in term $t$.

First, we define De Bruijn terms:

$t ::= n \mid \lambda t \mid t_1 \; t_2 \quad \text{where } n \in \mathbb{N}$



A term can be a natural number representing a variable, a lambda abstraction containing a term, or an application of one term to another.

The natural number represents the number of lambdas outward given a variable in a term before reaching the lambda that binds the variable.  

When substition occurs, the free variables in the resulting term must maintain their original bindings. Since substitution can place terms under additional lambda abstractions, we need to adjust the indices of free variables to prevent them from being accidentally captured by these new lambdas. 

To renumber the indices of free variables in a term, we define a shift operation. The shift operation $\uparrow^d_c$ ("lift by d starting at c") is:

$$\uparrow^d_c k = \begin{cases}
k & \text{if } k < c \\
k + d & \text{if } k \geq c
\end{cases}$$

$\uparrow^d_c (\lambda t) = \lambda(\uparrow^d_{c+1} t)$

$\uparrow^d_c (t_1 \; t_2) = (\uparrow^d_c t_1) \; (\uparrow^d_c t_2)$


Then, we define substitution by cases:

For variables:

$$[j \mapsto s]k = \begin{cases}
s & \text{if } k = j \\
k & \text{if } k \neq j
\end{cases}$$

For abstractions:
$[j \mapsto s](\lambda t) = \lambda([j+1 \mapsto \uparrow^1_0 s]t)$

For applications:
$[j \mapsto s](t_1 \ t_2) = ([j \mapsto s]t_1) \ ([j \mapsto s]t_2)$


## 2. Haskell Implementation

Here's the direct implementation of the formal definition above:

```haskell
module DeBruijn where

-- | De Bruijn terms
data DBTerm = DBVar Int    -- ^ Variables with numeric indices
            | DBLam DBTerm  -- ^ Lambda abstractions
            | DBApp DBTerm DBTerm  -- ^ Applications
            deriving (Show, Eq)

-- | Shift operation: ↑ⁿₖ t
-- Implements ↑ⁿₖ from the formal definition
shift :: Int  -- ^ Amount to shift (d)
     -> Int   -- ^ Cutoff (c)
     -> DBTerm -> DBTerm
shift d c (DBVar k)   =  if k < c then DBVar k else DBVar (k+d)
shift d c (DBLam t)   = DBLam $ shift d (c + 1) t
shift d c (DBApp t1 t2) = DBApp (shift d c t1) (shift d c t2)

-- | Substitution operation: [j → s]t
-- Implements [j → s]t from the formal definition
substitute :: Int    -- ^ Index to substitute (j)
          -> DBTerm  -- ^ Term to substitute (s)
          -> DBTerm  -- ^ Term to substitute in (t)
          -> DBTerm
substitute j (DBVar s) (DBVar k)   = if k == j then DBVar s else DBVar k
substitute j (DBVar s) (DBLam t)   = DBLam $ substitute (j+1) (shift 1 0 (DBVar s)) t 
substitute j (DBVar s) (DBApp t1 t2) = DBApp (substitute j (DBVar s) t1) (substitute j (DBVar s) t2)
```

## 3. Examples

[Haskell playground with examples](https://play.haskell.org/saved/0Yur72ed)

### Example 1: Simple Variable Substitution

Mathematical: $[0 \mapsto 1]0 = 1$

Haskell:
```haskell
test1 = substitute 0 (DBVar 1) (DBVar 0)
-- result is DBVar 1
```

### Example 2: Under Lambda

Mathematical: $[0 \mapsto 1](\lambda. 0) = \lambda. 0$

This derivation shows why bound variables don't get substituted:

$ [0 \mapsto 1](\lambda. 0) = \lambda([1 \mapsto \uparrow^1_0 1]0) = \lambda. 0 $

Haskell:
```haskell
test2 = substitute 0 (DBVar 1) (DBLam (DBVar 0))
-- result is DBLam (DBVar 0)
```

### Example 3: Application

Mathematical: $[0 \mapsto 1](0 \; 2) = (1 \; 2)$

Haskell:
```haskell
test3 = substitute 0 (DBVar 1) (DBApp (DBVar 0) (DBVar 2))
-- result is DBApp (DBVar 1) (DBVar 2)
```