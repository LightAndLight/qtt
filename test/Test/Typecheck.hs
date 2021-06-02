{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE TypeApplications #-}

module Test.Typecheck where

import Prelude hiding (pi)

import Bound.Context (Context)
import qualified Bound.Context as Context
import qualified Data.Map as Map
import Test.Hspec

import Context
import Syntax
import TypeError
import Typecheck

import Test.Utils

doCheckType ::
  (String -> Maybe (Entry String String String)) ->
  [(String, Usage)] ->
  Term String String String ->
  Ty String String String ->
  Either (TypeError String String) (Context String Usage)
doCheckType a b = checkType (Env id id a $ Context.fromList b)

doCheckTerm ::
  (String -> Maybe (Entry String String String)) ->
  [(String, Usage)] ->
  Term String String String ->
  Ty String String String ->
  Either (TypeError String String) (Context String Usage)
doCheckTerm a b = checkTerm (Env id id a $ Context.fromList b)

typecheckSpec :: Spec
typecheckSpec =
  describe "typecheck" $ do
    it "1) (\\A => \\x => x) :0 (A :0 Type) -> (x :1 A) -> A" $
      assertRight $
        doCheckType
          (const Nothing)
          []
          (lam "A" $ lam "x" $ pure "x")
          (forall_ ("A", Type) $ lpi ("x", pure "A") $ pure "A")
    it "2) (\\A => \\x => x) :1 (A :0 Type) -> (x :1 A) -> A" $
      assertRight $
        doCheckTerm
          (const Nothing)
          []
          (lam "A" $ lam "x" $ pure "x")
          (forall_ ("A", Type) $ lpi ("x", pure "A") $ pure "A")
    it "4) (\\A => \\x => x) :0 (A :0 Type) -> (x :0 A) -> A" $
      assertRight $
        doCheckType
          (const Nothing)
          []
          (lam "A" $ lam "x" $ pure "x")
          (forall_ ("A", Type) $ forall_ ("x", pure "A") $ pure "A")
    it "5) (\\A => \\x => x) :1 (A :0 Type) -> (x :0 A) -> A   invalid" $
      assertLeft (UsingErased "x") $
        doCheckTerm
          (const Nothing)
          []
          (lam "A" $ lam "x" $ pure "x")
          (forall_ ("A", Type) $ forall_ ("x", pure "A") $ pure "A")
    it "7) (\\A => \\x => \\y => y) :1 (A :0 Type) -> (x :1 A) -> (y :w A) -> A   invalid" $
      assertLeft
        (UnusedLinear "x")
        ( doCheckTerm
            (const Nothing)
            []
            (lam "A" $ lam "x" $ lam "y" $ pure "y")
            ( forall_ ("A", Type) $
                lpi ("x", pure "A") $
                  pi ("y", pure "A") $
                    pure "A"
            )
        )
    it "8) (\\A => \\x => x) :1 (A :1 Type) -> (x :1 A) -> A   invalid" $
      assertLeft
        (UnusedLinear "A")
        ( doCheckTerm
            (const Nothing)
            []
            (lam "A" $ lam "x" $ pure "x")
            ( lpi ("A", Type) $
                lpi ("x", pure "A") $
                  pure "A"
            )
        )
    it "9) (\\A => \\x => (x, x)) :1 (A :0 Type) -> (x :1 A) -> (_ : A ⨂ A)   invalid" $
      assertLeft
        (OverusedLinear "x")
        ( doCheckTerm
            (const Nothing)
            []
            (lam "A" $ lam "x" $ MkTensor (pure "x") (pure "x"))
            ( forall_ ("A", Type) $
                lpi ("x", pure "A") $
                  tensor ("_", Many, pure "A") (pure "A")
            )
        )
    it "10) (\\A => \\x => (x, x)) :1 (A :0 Type) -> (x :w A) -> (_ : A ⨂ A)" $
      assertRight
        ( doCheckTerm
            (const Nothing)
            []
            (lam "A" $ lam "x" $ MkTensor (pure "x") (pure "x"))
            ( forall_ ("A", Type) $
                pi ("x", pure "A") $
                  tensor ("_", Many, pure "A") (pure "A")
            )
        )
    it "11) (\\x => let (a, b) = x in a b) :1 (x : (_ : A -> B ⨂ A)) -> B   invalid" $
      {-
      Why? In a relevant context (the :1 judgement), a tensor is always linear in its
      second component.
      -}
      assertLeft
        (OverusedLinear "b")
        ( doCheckTerm
            ( \case
                "A" -> Just $ BindingEntry Type
                "B" -> Just $ BindingEntry Type
                _ -> Nothing
            )
            [ ("A", Zero)
            , ("B", Zero)
            ]
            (lam "x" $ unpackTensor ("a", "b") (pure "x") (App (pure "a") (pure "b")))
            ( pi ("_", tensor ("_", Many, pure "A" `arr` pure "B") (pure "A")) $
                pure "B"
            )
        )
    it "11.1) (\\x => let (a, b) = x in a b) :1 (x : (_ : A -o B ⨂ A)) -> B" $
      -- For something like 11) to go through, the function in the first component must use its
      -- argument linearly or irrelevantly
      assertRight
        ( doCheckTerm
            ( \case
                "A" -> Just $ BindingEntry Type
                "B" -> Just $ BindingEntry Type
                _ -> Nothing
            )
            [ ("A", Zero)
            , ("B", Zero)
            ]
            (lam "x" $ unpackTensor ("a", "b") (pure "x") (App (pure "a") (pure "b")))
            ( pi ("_", tensor ("_", Many, pure "A" `limp` pure "B") (pure "A")) $
                pure "B"
            )
        )
    it "12) (\\x => let (a, b) = x in a) :1 (x : (_ : A ⨂ A)) -o A   invalid" $
      assertLeft
        (UnusedLinear "b")
        ( doCheckTerm
            ( \case
                "A" -> Just $ BindingEntry Type
                _ -> Nothing
            )
            [("A", Zero)]
            (lam "x" $ unpackTensor ("a", "b") (pure "x") (pure "a"))
            ( limp (tensor ("_", Many, pure "A") (pure "A")) $
                pure "A"
            )
        )
    it "13) (\\x => let (a, b) = x in b) :1 (x : (_ :0 A ⨂ A)) -> A" $
      assertRight
        ( doCheckTerm
            ( \case
                "A" -> Just $ BindingEntry Type
                _ -> Nothing
            )
            [("A", Zero)]
            (lam "x" $ unpackTensor ("a", "b") (pure "x") (pure "b"))
            ( arr (tensor ("_", Zero, pure "A") (pure "A")) $
                pure "A"
            )
        )
    it "13.1) (\\x => let (a, b) = x in b) :1 (x : (_ :1 A ⨂ A)) -> A   invalid" $
      assertLeft
        (UnusedLinear "a")
        ( doCheckTerm
            ( \case
                "A" -> Just $ BindingEntry Type
                _ -> Nothing
            )
            [("A", Zero)]
            (lam "x" $ unpackTensor ("a", "b") (pure "x") (pure "b"))
            ( arr (tensor ("_", One, pure "A") (pure "A")) $
                pure "A"
            )
        )
    it "13.2) (\\x => let (a, b) = x in b) :1 (x : (_ : A ⨂ A)) -> A" $
      assertRight
        ( doCheckTerm
            ( \case
                "A" -> Just $ BindingEntry Type
                _ -> Nothing
            )
            [("A", Zero)]
            (lam "x" $ unpackTensor ("a", "b") (pure "x") (pure "b"))
            ( arr (tensor ("_", Many, pure "A") (pure "A")) $
                pure "A"
            )
        )
    it "13.3) (\\x => let (a, b) = x in a) :1 (x : (_ : A ⨂ A)) -> A   invalid" $
      assertLeft
        (UnusedLinear "b")
        ( doCheckTerm
            ( \case
                "A" -> Just $ BindingEntry Type
                _ -> Nothing
            )
            [("A", Zero)]
            (lam "x" $ unpackTensor ("a", "b") (pure "x") (pure "a"))
            ( arr (tensor ("_", Many, pure "A") (pure "A")) $
                pure "A"
            )
        )
    it "14) (\\x => fst x) :1 (x : (_ : A & A)) -o A" $
      assertRight
        ( doCheckTerm
            ( \case
                "A" -> Just $ BindingEntry Type
                _ -> Nothing
            )
            [("A", Zero)]
            (lam "x" $ Fst $ pure "x")
            ( limp (with ("_", pure "A") (pure "A")) $
                pure "A"
            )
        )
    it "15) (\\x => snd x) :1 (x : (_ : A & A)) -o A" $
      assertRight
        ( doCheckTerm
            ( \case
                "A" -> Just $ BindingEntry Type
                _ -> Nothing
            )
            [("A", Zero)]
            (lam "x" $ Snd $ pure "x")
            ( limp (with ("_", pure "A") (pure "A")) $
                pure "A"
            )
        )
    it "16) (\\x => (fst x, snd x)) :1 (x : (_ : A & B)) -o (_ : A & B)" $
      assertRight
        ( doCheckTerm
            ( \case
                "A" -> Just $ BindingEntry Type
                "B" -> Just $ BindingEntry Type
                _ -> Nothing
            )
            [ ("A", Zero)
            , ("B", Zero)
            ]
            (lam "x" $ MkWith (Fst $ pure "x") (Snd $ pure "x"))
            ( limp (with ("_", pure "A") (pure "B")) $
                with ("_", pure "A") (pure "B")
            )
        )
    it "17) (\\x => (x, x)) :1 (x : A) -o (_ : A & A)" $
      assertRight
        ( doCheckTerm
            ( \case
                "A" -> Just $ BindingEntry Type
                _ -> Nothing
            )
            [("A", Zero)]
            (lam "x" $ MkWith (pure "x") (pure "x"))
            ( limp (pure "A") $
                with ("_", pure "A") (pure "A")
            )
        )
    it "18) (\\x => let (a, b) = x in (a, b)) :1 (x : (_ : A ⨂ B)) -> (_ : A & B)" $
      assertRight
        ( doCheckTerm
            ( \case
                "A" -> Just $ BindingEntry Type
                _ -> Nothing
            )
            [("A", Zero)]
            ( lam "x" $
                unpackTensor ("a", "b") (pure "x") $
                  MkWith (pure "a") (pure "b")
            )
            ( arr (tensor ("_", Many, pure "A") (pure "B")) $
                with ("_", pure "A") (pure "B")
            )
        )
    it "19) (\\x => (fst x, snd x)) :1 (x : (_ : A & B)) -> (_ : A ⨂ B)" $
      assertRight
        ( doCheckTerm
            ( \case
                "A" -> Just $ BindingEntry Type
                _ -> Nothing
            )
            [("A", Zero)]
            ( lam "x" $
                MkTensor (Fst $ pure "x") (Snd $ pure "x")
            )
            ( arr (with ("_", pure "A") (pure "B")) $
                tensor ("_", Many, pure "A") (pure "B")
            )
        )
    it "20) (\\x => let (a, b) = x in (a, b)) :1 (x : (_ : A ⨂ B)) -o (_ : A & B)" $
      assertRight
        ( doCheckTerm
            ( \case
                "A" -> Just $ BindingEntry Type
                _ -> Nothing
            )
            [("A", Zero)]
            ( lam "x" $
                unpackTensor ("a", "b") (pure "x") $
                  MkWith (pure "a") (pure "b")
            )
            ( limp (tensor ("_", Many, pure "A") (pure "B")) $
                with ("_", pure "A") (pure "B")
            )
        )
    it "21) (\\x => (fst x, snd x)) :1 (x : (_ : A & B)) -o (_ : A ⨂ B)  invalid" $
      assertLeft
        (OverusedLinear "x")
        ( doCheckTerm
            ( \case
                "A" -> Just $ BindingEntry Type
                _ -> Nothing
            )
            [("A", Zero)]
            ( lam "x" $
                MkTensor (Fst $ pure "x") (Snd $ pure "x")
            )
            ( limp (with ("_", pure "A") (pure "B")) $
                tensor ("_", Many, pure "A") (pure "B")
            )
        )
    it "22) (\\x => \\f => f x) :1 ∀(x : A), (f : A -> B) -> B   invalid" $
      assertLeft
        (UsingErased "x")
        ( doCheckTerm
            ( \case
                "A" -> Just $ BindingEntry Type
                "B" -> Just $ BindingEntry Type
                _ -> Nothing
            )
            [ ("A", Zero)
            , ("B", Zero)
            ]
            ( lam "x" $
                lam "f" $
                  App (pure "f") (pure "x")
            )
            ( forall_ ("x", pure "A") $
                arr (arr (pure "A") (pure "B")) $
                  pure "B"
            )
        )
    it "23) (\\x => \\f => f x) :1 A -> (b : ∀(a : A) -> B) -> B" $
      assertRight
        ( doCheckTerm
            ( \case
                "A" -> Just $ BindingEntry Type
                "B" -> Just $ BindingEntry Type
                _ -> Nothing
            )
            [ ("A", Zero)
            , ("B", Zero)
            ]
            ( lam "x" $
                lam "f" $
                  App (pure "f") (pure "x")
            )
            ( arr (pure "A") $
                pi ("b", forall_ ("a", pure "A") (pure "B")) $
                  pure "B"
            )
        )
    it "24) List : Type -> Type, Nil : ∀(a : Type) -> List a |- Nil A :1 List A" $ do
      let nilType =
            forall_ ("a", Type) $
              App (pure "List") (pure "a")
          consType =
            forall_ ("a", Type) $
              arr (pure "a") $
                arr (App (pure "List") (pure "a")) $
                  App (pure "List") (pure "a")

      assertRight
        ( doCheckTerm
            ( \case
                "List" ->
                  Just $
                    InductiveEntry
                      (arr Type Type)
                      ( Map.fromList
                          [ ("Nil", nilType)
                          , ("Cons", consType)
                          ]
                      )
                "Nil" -> Just . CtorEntry $ nilType
                "Cons" -> Just . CtorEntry $ consType
                "A" -> Just $ BindingEntry Type
                _ -> Nothing
            )
            [ ("List", Many)
            , ("Nil", Many)
            , ("Cons", Many)
            , ("A", Zero)
            ]
            (App (pure "Nil") (pure "A"))
            (App (pure "List") (pure "A"))
        )
    it "25) Bool : Type, True : Bool, False : Bool, x : Bool  |- (case x of { True => False; False => True }) :1 Bool" $ do
      let falseType = pure "Bool"
          trueType = pure "Bool"

      assertRight
        ( doCheckTerm
            ( \case
                "Bool" ->
                  Just $
                    InductiveEntry
                      Type
                      ( Map.fromList
                          [ ("False", falseType)
                          , ("True", trueType)
                          ]
                      )
                "False" -> Just . CtorEntry $ falseType
                "True" -> Just . CtorEntry $ trueType
                "x" -> Just $ BindingEntry $ pure "Bool"
                _ -> Nothing
            )
            [ ("Bool", Many)
            , ("False", Many)
            , ("True", Many)
            , ("x", Many)
            ]
            ( Case
                (pure "x")
                [ ctorb "True" [] $ pure "False"
                , ctorb "False" [] $ pure "True"
                ]
            )
            (pure "Bool")
        )
    it "26) A : Type, B : Type, x : (_ : A & B)  |- (case x of { y => y }) :1 (_ : A & B)" $ do
      assertRight
        ( doCheckTerm
            ( \case
                "A" -> Just . BindingEntry $ Type
                "B" -> Just . BindingEntry $ Type
                "x" -> Just $ BindingEntry $ with ("_", pure "A") (pure "B")
                _ -> Nothing
            )
            [ ("A", Zero)
            , ("B", Zero)
            , ("x", Many)
            ]
            ( Case
                (pure "x")
                [ varb "y" $ pure "y"
                ]
            )
            (with ("_", pure "A") (pure "B"))
        )
    it "27) ..., BoolS : Bool -> Type, TrueS : BoolS True, FalseS : BoolS False, b : Bool, x : BoolS b  |- (case x of { TrueS => TrueS; FalseS => FalseS }) :1 BoolS b" $ do
      let falseType = pure "Bool"
          trueType = pure "Bool"
          falseSType = App (pure "BoolS") (pure "False")
          trueSType = App (pure "BoolS") (pure "True")

      assertRight
        ( doCheckTerm
            ( \case
                "Bool" ->
                  Just $
                    InductiveEntry
                      Type
                      ( Map.fromList
                          [ ("False", falseType)
                          , ("True", trueType)
                          ]
                      )
                "False" -> Just . CtorEntry $ falseType
                "True" -> Just . CtorEntry $ trueType
                "BoolS" ->
                  Just $
                    InductiveEntry
                      (arr (pure "Bool") Type)
                      ( Map.fromList
                          [ ("FalseS", falseSType)
                          , ("TrueS", trueSType)
                          ]
                      )
                "FalseS" -> Just . CtorEntry $ falseSType
                "TrueS" -> Just . CtorEntry $ trueSType
                "b" -> Just $ BindingEntry $ pure "Bool"
                "x" -> Just $ BindingEntry $ App (pure "BoolS") (pure "b")
                _ -> Nothing
            )
            [ ("Bool", Many)
            , ("False", Many)
            , ("True", Many)
            , ("BoolS", Many)
            , ("FalseS", Many)
            , ("TrueS", Many)
            , ("b", Zero)
            , ("x", Many)
            ]
            ( Case
                (pure "x")
                [ ctorb "TrueS" [] $ pure "TrueS"
                , ctorb "FalseS" [] $ pure "FalseS"
                ]
            )
            (App (pure "BoolS") (pure "b"))
        )
    it "28) ..., BoolS : Bool -> Type, TrueS : BoolS True, FalseS : BoolS False, b : Bool, x : BoolS b  |- (case x of { TrueS => TrueS; FalseS => TrueS }) :1 BoolS b   invalid" $ do
      let falseType = pure "Bool"
          trueType = pure "Bool"
          falseSType = App (pure "BoolS") (pure "False")
          trueSType = App (pure "BoolS") (pure "True")

      assertLeft
        ( TypeMismatch
            (App (pure "BoolS") (pure "False"))
            (App (pure "BoolS") (pure "True"))
        )
        ( doCheckTerm
            ( \case
                "Bool" ->
                  Just $
                    InductiveEntry
                      Type
                      ( Map.fromList
                          [ ("False", falseType)
                          , ("True", trueType)
                          ]
                      )
                "False" -> Just . CtorEntry $ falseType
                "True" -> Just . CtorEntry $ trueType
                "BoolS" ->
                  Just $
                    InductiveEntry
                      (arr (pure "Bool") Type)
                      ( Map.fromList
                          [ ("FalseS", falseSType)
                          , ("TrueS", trueSType)
                          ]
                      )
                "FalseS" -> Just . CtorEntry $ falseSType
                "TrueS" -> Just . CtorEntry $ trueSType
                "b" -> Just $ BindingEntry $ pure "Bool"
                "x" -> Just $ BindingEntry $ App (pure "BoolS") (pure "b")
                _ -> Nothing
            )
            [ ("Bool", Many)
            , ("False", Many)
            , ("True", Many)
            , ("BoolS", Many)
            , ("FalseS", Many)
            , ("TrueS", Many)
            , ("b", Zero)
            , ("x", Many)
            ]
            ( Case
                (pure "x")
                [ ctorb "TrueS" [] $ pure "TrueS"
                , ctorb "FalseS" [] $ pure "TrueS"
                ]
            )
            (App (pure "BoolS") (pure "b"))
        )
    it "29) ..., BoolS : Bool -> Type, TrueS : BoolS True, FalseS : BoolS False, x : BoolS True  |- (case x of { TrueS => TrueS; FalseS impossible }) :1 BoolS b" $ do
      let falseType = pure "Bool"
          trueType = pure "Bool"
          falseSType = App (pure "BoolS") (pure "False")
          trueSType = App (pure "BoolS") (pure "True")

      assertRight
        ( doCheckTerm
            ( \case
                "Bool" ->
                  Just $
                    InductiveEntry
                      Type
                      ( Map.fromList
                          [ ("False", falseType)
                          , ("True", trueType)
                          ]
                      )
                "False" -> Just . CtorEntry $ falseType
                "True" -> Just . CtorEntry $ trueType
                "BoolS" ->
                  Just $
                    InductiveEntry
                      (arr (pure "Bool") Type)
                      ( Map.fromList
                          [ ("FalseS", falseSType)
                          , ("TrueS", trueSType)
                          ]
                      )
                "FalseS" -> Just . CtorEntry $ falseSType
                "TrueS" -> Just . CtorEntry $ trueSType
                "x" -> Just $ BindingEntry $ App (pure "BoolS") (pure "True")
                _ -> Nothing
            )
            [ ("Bool", Many)
            , ("False", Many)
            , ("True", Many)
            , ("BoolS", Many)
            , ("FalseS", Many)
            , ("TrueS", Many)
            , ("x", Many)
            ]
            ( Case
                (pure "x")
                [ ctorb "TrueS" [] $ pure "TrueS"
                , ctorb_imp "FalseS" []
                ]
            )
            (App (pure "BoolS") (pure "True"))
        )
    it "30) Pair : Type -> Type -> Type, MkPair : (A : Type) -> (B : Type) -> (x : A) -> (y : B) -> Pair A B, A :0 Type, B :0 Type, x :1 Pair A B  |- (case x of { MkPair A B a b => a }) :1 A" $ do
      let mkPairType =
            forall_ ("A", Type) $
              forall_ ("B", Type) $
                pi ("x", pure "A") $
                  pi ("y", pure "B") $
                    App (App (pure "Pair") (pure "A")) (pure "B")

      assertRight
        ( doCheckTerm
            ( \case
                "Pair" ->
                  Just $
                    InductiveEntry
                      (arr Type $ arr Type Type)
                      ( Map.fromList
                          [ ("MkPair", mkPairType)
                          ]
                      )
                "MkPair" -> Just . CtorEntry $ mkPairType
                "A" -> Just $ BindingEntry $ Type
                "B" -> Just $ BindingEntry $ Type
                "x" -> Just $ BindingEntry $ App (App (pure "Pair") (pure "A")) (pure "B")
                _ -> Nothing
            )
            [ ("Pair", Many)
            , ("MkPair", Many)
            , ("A", Zero)
            , ("B", Zero)
            , ("x", One)
            ]
            ( Case
                (pure "x")
                [ ctorb "MkPair" ["A", "B", "x", "y"] $ pure "x"
                ]
            )
            (pure "A")
        )
    it "30.1) Pair : Type -> Type -> Type, MkPair : (A : Type) -> (B : Type) -> (x : A) -o (y : B) -o Pair A B, A :0 Type, B :0 Type, x :1 Pair A B  |- (case x of { MkPair A B a b => a }) :1 A   invalid" $ do
      let mkPairType =
            forall_ ("A", Type) $
              forall_ ("B", Type) $
                limp (pure "A") $
                  limp (pure "B") $
                    App (App (pure "Pair") (pure "A")) (pure "B")

      assertLeft
        (UnusedLinear "y")
        ( doCheckTerm
            ( \case
                "Pair" ->
                  Just $
                    InductiveEntry
                      (arr Type $ arr Type Type)
                      ( Map.fromList
                          [ ("MkPair", mkPairType)
                          ]
                      )
                "MkPair" -> Just . CtorEntry $ mkPairType
                "A" -> Just $ BindingEntry $ Type
                "B" -> Just $ BindingEntry $ Type
                "x" -> Just $ BindingEntry $ App (App (pure "Pair") (pure "A")) (pure "B")
                _ -> Nothing
            )
            [ ("Pair", Many)
            , ("MkPair", Many)
            , ("A", Zero)
            , ("B", Zero)
            , ("x", One)
            ]
            ( Case
                (pure "x")
                [ ctorb "MkPair" ["A", "B", "x", "y"] $ pure "x"
                ]
            )
            (pure "A")
        )
    it "30.2) Pair : Type -> Type -> Type, MkPair : (A : Type) -> (B : Type) -> (x : A) -> (y : B) -> Pair A B, A :0 Type, B :0 Type, a :1 A, b :1 B  |- MkPair A B a b :1 Pair A B   invalid" $ do
      let mkPairType =
            forall_ ("A", Type) $
              forall_ ("B", Type) $
                pi ("x", pure "A") $
                  pi ("y", pure "B") $
                    App (App (pure "Pair") (pure "A")) (pure "B")

      assertLeft
        (OverusedLinear "a")
        ( doCheckTerm
            ( \case
                "Pair" ->
                  Just $
                    InductiveEntry
                      (arr Type $ arr Type Type)
                      ( Map.fromList
                          [ ("MkPair", mkPairType)
                          ]
                      )
                "MkPair" -> Just . CtorEntry $ mkPairType
                "A" -> Just $ BindingEntry $ Type
                "B" -> Just $ BindingEntry $ Type
                "a" -> Just $ BindingEntry $ pure "A"
                "b" -> Just $ BindingEntry $ pure "B"
                _ -> Nothing
            )
            [ ("Pair", Many)
            , ("MkPair", Many)
            , ("A", Zero)
            , ("B", Zero)
            , ("a", One)
            , ("b", One)
            ]
            (App (App (App (App (pure "MkPair") (pure "A")) (pure "B")) (pure "a")) (pure "b"))
            (App (App (pure "Pair") (pure "A")) (pure "B"))
        )
    it "31) Pair : Type -> Type -> Type, MkPair : (A :0 Type) -> (B :0 Type) -> (x : A) -> (y : B) -> Pair A B, A :0 Type, B :0 Type, x :1 Pair A B  |- (case x of { MkPair A B a b => A }) :1 Type   invalid" $ do
      let mkPairType =
            forall_ ("A", Type) $
              forall_ ("B", Type) $
                pi ("x", pure "A") $
                  pi ("y", pure "B") $
                    App (App (pure "Pair") (pure "A")) (pure "B")

      assertLeft
        (UsingErased "A")
        ( doCheckTerm
            ( \case
                "Pair" ->
                  Just $
                    InductiveEntry
                      (arr Type $ arr Type Type)
                      ( Map.fromList
                          [ ("MkPair", mkPairType)
                          ]
                      )
                "MkPair" -> Just . CtorEntry $ mkPairType
                "A" -> Just $ BindingEntry $ Type
                "B" -> Just $ BindingEntry $ Type
                "x" -> Just $ BindingEntry $ App (App (pure "Pair") (pure "A")) (pure "B")
                _ -> Nothing
            )
            [ ("Pair", Many)
            , ("MkPair", Many)
            , ("A", Zero)
            , ("B", Zero)
            , ("x", One)
            ]
            ( Case
                (pure "x")
                [ ctorb "MkPair" ["A", "B", "x", "y"] $ pure "A"
                ]
            )
            Type
        )
    it "32) Pair : Type -> Type -> Type, MkPair : (A : Type) -> (B : Type) -> (x : A) -> (y : B) -> Pair A B, A :0 Type, B :0 Type, x :w Pair A B  |- (case x of { MkPair A B a b => a }) :1 A" $ do
      let mkPairType =
            forall_ ("A", Type) $
              forall_ ("B", Type) $
                pi ("x", pure "A") $
                  pi ("y", pure "B") $
                    App (App (pure "Pair") (pure "A")) (pure "B")

      assertRight
        ( doCheckTerm
            ( \case
                "Pair" ->
                  Just $
                    InductiveEntry
                      (arr Type $ arr Type Type)
                      ( Map.fromList
                          [ ("MkPair", mkPairType)
                          ]
                      )
                "MkPair" -> Just . CtorEntry $ mkPairType
                "A" -> Just $ BindingEntry $ Type
                "B" -> Just $ BindingEntry $ Type
                "x" -> Just $ BindingEntry $ App (App (pure "Pair") (pure "A")) (pure "B")
                _ -> Nothing
            )
            [ ("Pair", Many)
            , ("MkPair", Many)
            , ("A", Zero)
            , ("B", Zero)
            , ("x", Many)
            ]
            ( Case
                (pure "x")
                [ ctorb "MkPair" ["A", "B", "x", "y"] $ pure "x"
                ]
            )
            (pure "A")
        )
