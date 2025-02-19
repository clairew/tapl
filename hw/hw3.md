## HW 3

## Exercise 13.3.1 
To model garbage collection, first we define garbage collection as collecting and reusing finite memory that can no longer be reached by the program.

A location is reachable if the program can access the location by the current term evaluated or referenced by value in another reachable location. For the latter, to know if a location is reachable, we use the current term to find all reachable locations and look at their values which then lead to the locations their values reference, and so on - these sequences of following references must be finite (since we have finite store size) and together they make up term reachability - `reachable(t, μ)` - locations reachable from `locations(t)`. More specifically - when we have a reference type term, we look up its location in the store, which tells us what value is at that location. Otherwise we keep evaluating the term until we reach a reference type. To add garbage collection on top of the existing evaluation rules, `μ'` must be restricted to `reachable(t, μ)`. Finally, in order to identify the reachable locations, we restrict garbage collection to the outermost level so it won't miss references in unevaluated parts.

We would need to show that this definition of garbage collection doesn't change program behavior, reachability is preserved, and memory safety is maintained. 


## Exercise 13.5.8 from TAPL

We are able to write a well-typed, non-terminating factorial function due to by storing the factorial function in a reference. Note - see haskell playground for full implementation required to be able to write the function.

```
fact :: Term -- factorial function
fact = 
    Lam "n" TNat (
        If (IsZero (Var "n"))
           (Succ Zero)                        
           (App                               
             (App mult (Var "n"))
             (App fact (Pred (Var "n")))))

factRef = -- create a reference to store the factorial function
    App
        (Lam "r" (TRef (TArrow TNat TNat))
            -- store factorial in the reference
            (Assign (Var "r") fact))
        (Ref fact)  -- initialize with factorial
```

Haskell Playground link [here](https://play.haskell.org/saved/tpNdeKCa).

Uncomment `print [testFactRef]` - what will result is a timeout. Playground link includes the typing and evaluation rules needed.