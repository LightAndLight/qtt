module Test.Utils where

import Test.Hspec

assertRight :: HasCallStack => Show a => Either a b -> Expectation
assertRight a =
  case a of
    Right{} -> pure ()
    Left e -> expectationFailure $ show e

assertLeft :: HasCallStack => (Eq a, Show a) => a -> Either a b -> Expectation
assertLeft e a =
  case a of
    Right{} ->
      expectationFailure $
        "expected:\n\n" <> show e <> "\n\nbut got Right"
    Left e' -> e' `shouldBe` e