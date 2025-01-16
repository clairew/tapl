module UntypedLCTest where

import Test.QuickCheck
import Test.HUnit
import UntypedLC

-- Properties that should hold for alpha conversion
prop_alphaConvert_identity :: String -> String -> Property
prop_alphaConvert_identity from to =
    from /= to ==>
    alphaConvert from to (alphaConvert to from (Var from)) == Var from

-- Alpha conversion shouldn't change free variables that aren't being converted
prop_alphaConvert_free :: String -> String -> String -> Property
prop_alphaConvert_free from to other =
    from /= other && to /= other ==>
    alphaConvert from to (Var other) == Var other

-- Unit tests for concrete cases
tests = TestList [
    -- Test basic identity combinator
    TestCase $ assertEqual 
        "Alpha convert x to y in λx.x"
        (Lam "y" (Var "y"))
        (alphaConvert "x" "y" i),
    
    -- Test K combinator
    TestCase $ assertEqual
        "Alpha convert x to z in λx.λy.x"
        (Lam "z" (Lam "y" (Var "z")))
        (alphaConvert "x" "z" k),
        
    -- Test that free variables remain unchanged
    TestCase $ assertEqual
        "Alpha convert x to y in (λz.x)"
        (Lam "z" (Var "y"))
        (alphaConvert "x" "y" (Lam "z" (Var "x")))
    ]

-- Generate random terms for property testing
instance Arbitrary Term where
    arbitrary = sized arbitraryTerm
    
arbitraryTerm :: Int -> Gen Term
arbitraryTerm 0 = Var <$> arbitrary
arbitraryTerm n = oneof [
    Var <$> arbitrary,
    Lam <$> arbitrary <*> arbitraryTerm (n-1),
    App <$> arbitraryTerm (n `div` 2) <*> arbitraryTerm (n `div` 2)
    ]

-- Run all tests
main :: IO ()
main = do
    putStrLn "Running QuickCheck tests..."
    quickCheck prop_alphaConvert_identity
    quickCheck prop_alphaConvert_free
    putStrLn "Running unit tests..."
    runTestTT tests
