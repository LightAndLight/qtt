{-# language LambdaCase #-}
{-# language TypeApplications #-}
module Main where

import Prelude hiding (pi)
import Bound.Var (Var(..))
import Control.Monad.Trans.Class (lift)

import Test.Hspec

import Syntax
import Typecheck

assertRight :: Show a => Either a b -> Expectation
assertRight a =
  case a of
    Right{} -> pure ()
    Left e -> expectationFailure $ show e

assertLeft :: (Eq a, Show a) => a -> Either a b -> Expectation
assertLeft e a =
  case a of
    Right{} ->
      expectationFailure $
      "expected:\n\n" <> show e <> "\n\nbut got Right"
    Left e' -> e' `shouldBe` e

main :: IO ()
main =
  hspec $ do
    describe "typecheck" $ do
      it "(\\A => \\x => x) :0 (A :0 Type) -> (x :1 A) -> A" $
        assertRight $
        check @String @String Left Left
          (lam "A" $ lam "x" $ pure "x")
          Zero
          (pi ("A", Zero, Type) $ pi ("x", One, pure "A") $ pure "A")
      it "(\\A => \\x => x) :1 (A :0 Type) -> (x :1 A) -> A" $
        assertRight $
        check @String @String Left Left
          (lam "A" $ lam "x" $ pure "x")
          One
          (pi ("A", Zero, Type) $ pi ("x", One, pure "A") $ pure "A")
      it "(\\A => \\x => x) :w (A :0 Type) -> (x :1 A) -> A" $
        assertRight $
        check @String @String Left Left
          (lam "A" $ lam "x" $ pure "x")
          Many
          (pi ("A", Zero, Type) $ pi ("x", One, pure "A") $ pure "A")
      it "(\\A => \\x => x) :0 (A :0 Type) -> (x :0 A) -> A" $
        assertRight $
        check @String @String Left Left
          (lam "A" $ lam "x" $ pure "x")
          Zero
          (pi ("A", Zero, Type) $ pi ("x", Zero, pure "A") $ pure "A")
      it "(\\A => \\x => x) :1 (A :0 Type) -> (x :0 A) -> A   invalid" $
        assertLeft (Deep1 $ Deep1 $ UsingErased $ B ()) $
        check @String @String Left Left
          (lam "A" $ lam "x" $ pure "x")
          One
          (pi ("A", Zero, Type) $ pi ("x", Zero, pure "A") $ pure "A")
      it "(\\A => \\x => x) :w (A :0 Type) -> (x :0 A) -> A   invalid" $
        assertLeft (Deep1 $ Deep1 $ UsingErased $ B ()) $
        check @String @String Left Left
          (lam "A" $ lam "x" $ pure "x")
          Many
          (pi ("A", Zero, Type) $ pi ("x", Zero, pure "A") $ pure "A")
      it "(\\A => \\x => \\y => x) :w (A :0 Type) -> (x :1 A) -> (y :w A) -> A   invalid" $
        assertLeft
          (Deep1 . Deep1 . UnusedLinear $ B ())
          (check @String @String Left Left
            (lam "A" $ lam "x" $ lam "y" $ pure "y")
            Many
            (pi ("A", Zero, Type) $
             pi ("x", One, pure "A") $
             pi ("y", Many, pure "A") $
             pure "A"))
      it "(\\A => \\x => x) :w (A :1 Type) -> (x :1 A) -> A   invalid" $
        assertLeft
          (Deep1 $ UnusedLinear $ B ())
          (check @String @String Left Left
            (lam "A" $ lam "x" $ pure "x")
            Many
            (pi ("A", One, Type) $
             pi ("x", One, pure "A") $
             pure "A"))
      it "(\\A => \\x => (x, x)) :w (A :0 Type) -> (x :1 A) -> (y : A * A)   invalid" $
        assertLeft
          (Deep1 $ Deep1 $ UsingErased $ B ())
          (check @String @String Left Left
            (lam "A" $ lam "x" $ Pair (pure "x") (pure "x"))
            Many
            (pi ("A", Zero, Type) $
             pi ("x", One, pure "A") $
             Sigma (pure "A") (lift $ pure "A")))
      it "(\\A => \\x => (x, x)) :w (A :0 Type) -> (x :w A) -> (y : A * A)" $
        assertRight
          (check @String @String Left Left
            (lam "A" $ lam "x" $ Pair (pure "x") (pure "x"))
            Many
            (pi ("A", Zero, Type) $
             pi ("x", Many, pure "A") $
             Sigma (pure "A") (lift $ pure "A")))
      it "(\\x => let (a, b) = x in a b) :w (x : A -> B * A) -o B" $
        assertRight
          (check @String @String
             (\case
                 "A" -> Right Type
                 "B" -> Right Type
                 a -> Left a)
             (\case
                 "A" -> Right Zero
                 "B" -> Right Zero
                 a -> Left a)
             (lam "x" $ elimPair ("a", "b") (pure "x") (App (pure "a") (pure "b")))
             Many
             (limp (Sigma (pure "A" `arr` pure "B") (lift $ pure "A")) $
              pure "B"))
      it "(\\x => let (a, b) = x in a) :w (x : A * A) -o A   invalid" $
        assertLeft
          (Deep1 $ Deep2 $ UnusedLinear $ B True)
          (check @String @String
             (\case
                 "A" -> Right Type
                 a -> Left a)
             (\case
                 "A" -> Right Zero
                 a -> Left a)
             (lam "x" $ elimPair ("a", "b") (pure "x") (pure "a"))
             Many
             (limp (Sigma (pure "A") (lift $ pure "A")) $
              pure "A"))
      it "(\\x => let (a, b) = x in a) :w (x : A * A) -> A" $
        assertRight
          (check @String @String
             (\case
                 "A" -> Right Type
                 a -> Left a)
             (\case
                 "A" -> Right Zero
                 a -> Left a)
             (lam "x" $ elimPair ("a", "b") (pure "x") (pure "a"))
             Many
             (arr (Sigma (pure "A") (lift $ pure "A")) $
              pure "A"))
