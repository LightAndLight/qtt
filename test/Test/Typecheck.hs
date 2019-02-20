{-# language LambdaCase #-}
{-# language TypeApplications #-}
module Test.Typecheck where

import Prelude hiding (pi)

import Test.Hspec
import qualified Data.Map as Map

import Syntax
import Typecheck

import Test.Utils

doCheck ::
  (String -> Maybe (Entry String String String)) ->
  (String -> Maybe Usage) ->
  Term String String String ->
  Usage ->
  Ty String String String ->
  Either (TypeError String String) (String -> Maybe Usage)
doCheck = check id id

typecheckSpec :: Spec
typecheckSpec =
  describe "typecheck" $ do
    it "1) (\\A => \\x => x) :0 (A :0 Type) -> (x :1 A) -> A" $
      assertRight $
      doCheck (const Nothing) (const Nothing)
        (lam "A" $ lam "x" $ pure "x")
        Zero
        (forall_ ("A", Type) $ lpi ("x", pure "A") $ pure "A")
    it "2) (\\A => \\x => x) :1 (A :0 Type) -> (x :1 A) -> A" $
      assertRight $
      doCheck (const Nothing) (const Nothing)
        (lam "A" $ lam "x" $ pure "x")
        One
        (forall_ ("A", Type) $ lpi ("x", pure "A") $ pure "A")
    it "3) (\\A => \\x => x) :w (A :0 Type) -> (x :1 A) -> A" $
      assertRight $
      doCheck (const Nothing) (const Nothing)
        (lam "A" $ lam "x" $ pure "x")
        Many
        (forall_ ("A", Type) $ lpi ("x", pure "A") $ pure "A")
    it "4) (\\A => \\x => x) :0 (A :0 Type) -> (x :0 A) -> A" $
      assertRight $
      doCheck (const Nothing) (const Nothing)
        (lam "A" $ lam "x" $ pure "x")
        Zero
        (forall_ ("A", Type) $ forall_ ("x", pure "A") $ pure "A")
    it "5) (\\A => \\x => x) :1 (A :0 Type) -> (x :0 A) -> A   invalid" $
      assertLeft (UsingErased "x") $
      doCheck (const Nothing) (const Nothing)
        (lam "A" $ lam "x" $ pure "x")
        One
        (forall_ ("A", Type) $ forall_ ("x", pure "A") $ pure "A")
    it "6) (\\A => \\x => x) :w (A :0 Type) -> (x :0 A) -> A   invalid" $
      assertLeft (UsingErased "x") $
      doCheck (const Nothing) (const Nothing)
        (lam "A" $ lam "x" $ pure "x")
        Many
        (forall_ ("A", Type) $ forall_ ("x", pure "A") $ pure "A")
    it "7) (\\A => \\x => \\y => y) :w (A :0 Type) -> (x :1 A) -> (y :w A) -> A   invalid" $
      assertLeft
        (UnusedLinear "x")
        (doCheck (const Nothing) (const Nothing)
          (lam "A" $ lam "x" $ lam "y" $ pure "y")
          Many
          (forall_ ("A", Type) $
           lpi ("x", pure "A") $
           pi ("y", pure "A") $
           pure "A"))
    it "8) (\\A => \\x => x) :w (A :1 Type) -> (x :1 A) -> A   invalid" $
      assertLeft
        (UnusedLinear "A")
        (doCheck (const Nothing) (const Nothing)
          (lam "A" $ lam "x" $ pure "x")
          Many
          (lpi ("A", Type) $
           lpi ("x", pure "A") $
           pure "A"))
    it "9) (\\A => \\x => (x, x)) :w (A :0 Type) -> (x :1 A) -> (_ : A ⨂ A)   invalid" $
      assertLeft
        (UsingErased "x")
        (doCheck (const Nothing) (const Nothing)
          (lam "A" $ lam "x" $ MkTensor (pure "x") (pure "x"))
          Many
          (forall_ ("A", Type) $
           lpi ("x", pure "A") $
           tensor ("_", pure "A") (pure "A")))
    it "10) (\\A => \\x => (x, x)) :w (A :0 Type) -> (x :w A) -> (_ : A ⨂ A)" $
      assertRight
        (doCheck (const Nothing) (const Nothing)
          (lam "A" $ lam "x" $ MkTensor (pure "x") (pure "x"))
          Many
          (forall_ ("A", Type) $
           pi ("x", pure "A") $
           tensor ("_", pure "A") (pure "A")))
    it "11) (\\x => let (a, b) = x in a b) :w (x : (_ : A -> B ⨂ A)) -o B" $
      assertRight
        (doCheck
            (\case
                "A" -> Just $ BindingEntry Type
                "B" -> Just $ BindingEntry Type
                _ -> Nothing)
            (\case
                "A" -> Just Zero
                "B" -> Just Zero
                _ -> Nothing)
            (lam "x" $ unpackTensor ("a", "b") (pure "x") (App (pure "a") (pure "b")))
            Many
            (limp (tensor ("_", pure "A" `arr` pure "B") (pure "A")) $
             pure "B"))
    it "12) (\\x => let (a, b) = x in a) :w (x : (_ : A ⨂ A)) -o A   invalid" $
      assertLeft
        (UnusedLinear "b")
        (doCheck
            (\case
                "A" -> Just $ BindingEntry Type
                _ -> Nothing)
            (\case
                "A" -> Just Zero
                _ -> Nothing)
            (lam "x" $ unpackTensor ("a", "b") (pure "x") (pure "a"))
            Many
            (limp (tensor ("_", pure "A") (pure "A")) $
             pure "A"))
    it "13) (\\x => let (a, b) = x in a) :w (x : (_ : A ⨂ A)) -> A" $
      assertRight
        (doCheck
            (\case
                "A" -> Just $ BindingEntry Type
                _ -> Nothing)
            (\case
                "A" -> Just Zero
                _ -> Nothing)
            (lam "x" $ unpackTensor ("a", "b") (pure "x") (pure "a"))
            Many
            (arr (tensor ("_", pure "A") (pure "A")) $
            pure "A"))
    it "14) (\\x => fst x) :w (x : (_ : A & A)) -o A" $
      assertRight
        (doCheck
            (\case
                "A" -> Just $ BindingEntry Type
                _ -> Nothing)
            (\case
                "A" -> Just Zero
                _ -> Nothing)
            (lam "x" $ Fst $ pure "x")
            Many
            (limp (with ("_", pure "A") (pure "A")) $
            pure "A"))
    it "15) (\\x => snd x) :w (x : (_ : A & A)) -o A" $
      assertRight
        (doCheck
            (\case
                "A" -> Just $ BindingEntry Type
                _ -> Nothing)
            (\case
                "A" -> Just Zero
                _ -> Nothing)
            (lam "x" $ Snd $ pure "x")
            Many
            (limp (with ("_", pure "A") (pure "A")) $
             pure "A"))
    it "16) (\\x => (fst x, snd x)) :w (x : (_ : A & B)) -o (_ : A & B)" $
      assertRight
        (doCheck
            (\case
                "A" -> Just $ BindingEntry Type
                "B" -> Just $ BindingEntry Type
                _ -> Nothing)
            (\case
                "A" -> Just Zero
                "B" -> Just Zero
                _ -> Nothing)
            (lam "x" $ MkWith (Fst $ pure "x") (Snd $ pure "x"))
            Many
            (limp (with ("_", pure "A") (pure "B")) $
             with ("_", pure "A") (pure "B")))
    it "17) (\\x => (x, x)) :w (x : A) -o (_ : A & A)" $
      assertRight
        (doCheck
            (\case
                "A" -> Just $ BindingEntry Type
                _ -> Nothing)
            (\case
                "A" -> Just Zero
                _ -> Nothing)
            (lam "x" $ MkWith (pure "x") (pure "x"))
            Many
            (limp (pure "A") $
             with ("_", pure "A") (pure "A")))
    it "18) (\\x => let (a, b) = x in (a, b)) :w (x : (_ : A ⨂ B)) -> (_ : A & B)" $
      assertRight
        (doCheck
            (\case
                "A" -> Just $ BindingEntry Type
                _ -> Nothing)
            (\case
                "A" -> Just Zero
                _ -> Nothing)
            (lam "x" $
             unpackTensor ("a", "b") (pure "x") $
             MkWith (pure "a") (pure "b"))
            Many
            (arr (tensor ("_", pure "A") (pure "B")) $
             with ("_", pure "A") (pure "B")))
    it "19) (\\x => (fst x, snd x)) :w (x : (_ : A & B)) -> (_ : A ⨂ B)" $
      assertRight
        (doCheck
            (\case
                "A" -> Just $ BindingEntry Type
                _ -> Nothing)
            (\case
                "A" -> Just Zero
                _ -> Nothing)
            (lam "x" $
             MkTensor (Fst $ pure "x") (Snd $ pure "x"))
            Many
            (arr (with ("_", pure "A") (pure "B")) $
             tensor ("_", pure "A") (pure "B")))
    it "20) (\\x => let (a, b) = x in (a, b)) :w (x : (_ : A ⨂ B)) -o (_ : A & B)" $
      assertRight
        (doCheck
            (\case
                "A" -> Just $ BindingEntry Type
                _ -> Nothing)
            (\case
                "A" -> Just Zero
                _ -> Nothing)
            (lam "x" $
             unpackTensor ("a", "b") (pure "x") $
             MkWith (pure "a") (pure "b"))
            Many
            (limp (tensor ("_", pure "A") (pure "B")) $
             with ("_", pure "A") (pure "B")))
    it "21) (\\x => (fst x, snd x)) :w (x : (_ : A & B)) -o (_ : A ⨂ B)  invalid" $
      assertLeft
        (UsingErased "x")
        (doCheck
            (\case
                "A" -> Just $ BindingEntry Type
                _ -> Nothing)
            (\case
                "A" -> Just Zero
                _ -> Nothing)
            (lam "x" $
             MkTensor (Fst $ pure "x") (Snd $ pure "x"))
            Many
            (limp (with ("_", pure "A") (pure "B")) $
             tensor ("_", pure "A") (pure "B")))
    it "22) (\\x => \\f => f x) :w ∀(x : A), (f : A -> B) -> B   invalid" $
      assertLeft
        (UsingErased "x")
        (doCheck
            (\case
                "A" -> Just $ BindingEntry Type
                "B" -> Just $ BindingEntry Type
                _ -> Nothing)
            (\case
                "A" -> Just Zero
                "B" -> Just Zero
                _ -> Nothing)
            (lam "x" $
            lam "f" $
            App (pure "f") (pure "x"))
            Many
            (forall_ ("a", pure "A") $
             arr (arr (pure "A") (pure "B")) $
             pure "B"))
    it "23) (\\x => \\f => f x) :w A -> (b : ∀(a : A) -> B) -> B" $
      assertRight
        (doCheck
            (\case
                "A" -> Just $ BindingEntry Type
                "B" -> Just $ BindingEntry Type
                _ -> Nothing)
            (\case
                "A" -> Just Zero
                "B" -> Just Zero
                _ -> Nothing)
            (lam "x" $
             lam "f" $
             App (pure "f") (pure "x"))
            Many
            (arr (pure "A") $
             pi ("b", forall_ ("a", pure "A") (pure "B")) $
             pure "B"))
    it "24) List : Type -> Type, Nil : ∀(a : Type) -> List a |- Nil A :w List A" $ do
      let
        nilType =
          forall_ ("a", Type) $
          App (pure "List") (pure "a")
        consType =
          forall_ ("a", Type) $
          arr (pure "a") $
          arr (App (pure "List") (pure "a")) $
          App (pure "List") (pure "a")

      assertRight
        (doCheck
            (\case
                "List" ->
                  Just $
                  InductiveEntry
                    (arr Type Type)
                    (Map.fromList
                     [ ("Nil", nilType)
                     , ("Cons", consType)
                     ])
                "Nil" -> Just . BindingEntry $ nilType
                "Cons" -> Just . BindingEntry $ consType
                "A" -> Just $ BindingEntry Type
                _ -> Nothing)
            (\case
                "List" -> Just Many
                "Nil" -> Just Many
                "Cons" -> Just Many
                "A" -> Just Zero
                _ -> Nothing)
            (App (pure "Nil") (pure "A"))
            Many
            (App (pure "List") (pure "A")))
