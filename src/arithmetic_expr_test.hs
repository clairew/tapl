import ArithmeticExpr
import Test.HUnit

tests = TestList [
    TestCase (assertEqual "Simple True" (TTrue) (eval1 TTrue)),
    TestCase (assertEqual "If-True case" (TTrue) (eval1 (TIf TTrue TTrue TFalse)))
    ]

main :: IO Counts
main = runTestTT tests
