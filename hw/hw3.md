## HW 3

## Exercise 13.3.1 


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