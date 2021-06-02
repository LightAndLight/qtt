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
  [(String, Entry String String String)] ->
  [(String, Usage)] ->
  Term String String String ->
  Ty String String String ->
  Either (TypeError String String) (Context String Usage)
doCheckType a b = checkType (Env id id (Context.fromList a) (Context.fromList b))

doCheckTerm ::
  [(String, Entry String String String)] ->
  [(String, Usage)] ->
  Term String String String ->
  Ty String String String ->
  Either (TypeError String String) (Context String Usage)
doCheckTerm a b = checkTerm (Env id id (Context.fromList a) (Context.fromList b))

typecheckSpec :: Spec
typecheckSpec =
  describe "typecheck" $ do
    it "(\\A => \\x => x) :0 (A :0 Type) -> (x :1 A) -> A" $
      assertRight $
        doCheckType
          []
          []
          (lam "A" $ lam "x" $ pure "x")
          (forall_ ("A", Type) $ lpi ("x", pure "A") $ pure "A")
    it "(\\A => \\x => x) :1 (A :0 Type) -> (x :1 A) -> A" $
      assertRight $
        doCheckTerm
          []
          []
          (lam "A" $ lam "x" $ pure "x")
          (forall_ ("A", Type) $ lpi ("x", pure "A") $ pure "A")
    it "(\\A => \\x => x) :0 (A :0 Type) -> (x :0 A) -> A" $
      assertRight $
        doCheckType
          []
          []
          (lam "A" $ lam "x" $ pure "x")
          (forall_ ("A", Type) $ forall_ ("x", pure "A") $ pure "A")
    it "(\\A => \\x => x) :1 (A :0 Type) -> (x :0 A) -> A   invalid" $
      assertLeft (UsingErased "x") $
        doCheckTerm
          []
          []
          (lam "A" $ lam "x" $ pure "x")
          (forall_ ("A", Type) $ forall_ ("x", pure "A") $ pure "A")
    it "(\\A => \\x => \\y => y) :1 (A :0 Type) -> (x :1 A) -> (y :w A) -> A   invalid" $
      assertLeft
        (UnusedLinear "x")
        ( doCheckTerm
            []
            []
            (lam "A" $ lam "x" $ lam "y" $ pure "y")
            ( forall_ ("A", Type) $
                lpi ("x", pure "A") $
                  pi ("y", pure "A") $
                    pure "A"
            )
        )
    it "(\\A => \\x => \\y => x) :1 (A :0 Type) -> (x :1 A) -> (y :w A) -> A" $
      assertRight
        ( doCheckTerm
            []
            []
            (lam "A" $ lam "x" $ lam "y" $ pure "x")
            ( forall_ ("A", Type) $
                lpi ("x", pure "A") $
                  pi ("y", pure "A") $
                    pure "A"
            )
        )
    it "(\\A => \\x => x) :1 (A :1 Type) -> (x :1 A) -> A   invalid" $
      assertLeft
        (UnusedLinear "A")
        ( doCheckTerm
            []
            []
            (lam "A" $ lam "x" $ pure "x")
            ( lpi ("A", Type) $
                lpi ("x", pure "A") $
                  pure "A"
            )
        )
    it "(\\A => \\x => x) :1 (A :0 Type) -> (x :1 A) -> A" $
      assertRight
        ( doCheckTerm
            []
            []
            (lam "A" $ lam "x" $ pure "x")
            ( forall_ ("A", Type) $
                lpi ("x", pure "A") $
                  pure "A"
            )
        )
    it "(\\A => \\x => (x, x)) :1 (A :0 Type) -> (x :1 A) -> (_ : A ⨂ A)   invalid" $
      assertLeft
        (OverusedLinear "x")
        ( doCheckTerm
            []
            []
            (lam "A" $ lam "x" $ MkTensor (pure "x") (pure "x"))
            ( forall_ ("A", Type) $
                lpi ("x", pure "A") $
                  tensor ("_", Many, pure "A") (pure "A")
            )
        )
    it "(\\A => \\x => (x, x)) :1 (A :0 Type) -> (x :w A) -> (_ : A ⨂ A)" $
      assertRight
        ( doCheckTerm
            []
            []
            (lam "A" $ lam "x" $ MkTensor (pure "x") (pure "x"))
            ( forall_ ("A", Type) $
                pi ("x", pure "A") $
                  tensor ("_", Many, pure "A") (pure "A")
            )
        )
    it "(\\x => let (a, b) = x in a b) :1 (x : (_ : A -> B ⨂ A)) -> B   invalid" $
      {-
      Why? In a relevant context (the :1 judgement), a tensor is always linear in its
      second component. The linear `b` is passed to a function with an unrestricted
      argument, which means `b` is used too many times.
      -}
      assertLeft
        (OverusedLinear "b")
        ( doCheckTerm
            [ ("A", BindingEntry Type)
            , ("B", BindingEntry Type)
            ]
            [ ("A", Zero)
            , ("B", Zero)
            ]
            (lam "x" $ unpackTensor ("a", "b") (pure "x") (App (pure "a") (pure "b")))
            ( pi ("_", tensor ("_", Many, pure "A" `arr` pure "B") (pure "A")) $
                pure "B"
            )
        )
    it "(\\x => let (a, b) = x in a b) :1 (x : (_ : A -o B ⨂ A)) -> B" $
      -- The above to go through, the function in the first component must use its
      -- argument linearly or irrelevantly
      assertRight
        ( doCheckTerm
            [ ("A", BindingEntry Type)
            , ("B", BindingEntry Type)
            ]
            [ ("A", Zero)
            , ("B", Zero)
            ]
            (lam "x" $ unpackTensor ("a", "b") (pure "x") (App (pure "a") (pure "b")))
            ( pi ("_", tensor ("_", Many, pure "A" `limp` pure "B") (pure "A")) $
                pure "B"
            )
        )
    it "(\\x => let (a, b) = x in a) :1 (x : (_ : A ⨂ A)) -> A   invalid" $
      assertLeft
        (UnusedLinear "b")
        ( doCheckTerm
            [("A", BindingEntry Type)]
            [("A", Zero)]
            (lam "x" $ unpackTensor ("a", "b") (pure "x") (pure "a"))
            ( arr (tensor ("_", Many, pure "A") (pure "A")) $
                pure "A"
            )
        )
    it "(\\x => let (a, b) = x in b) :1 (x : (_ : A ⨂ A)) -> A" $
      assertRight
        ( doCheckTerm
            [("A", BindingEntry Type)]
            [("A", Zero)]
            (lam "x" $ unpackTensor ("a", "b") (pure "x") (pure "b"))
            ( arr (tensor ("_", Many, pure "A") (pure "A")) $
                pure "A"
            )
        )
    it "(\\x => let (a, b) = x in b) :1 (x : (_ :0 A ⨂ A)) -> A" $
      assertRight
        ( doCheckTerm
            [("A", BindingEntry Type)]
            [("A", Zero)]
            (lam "x" $ unpackTensor ("a", "b") (pure "x") (pure "b"))
            ( arr (tensor ("_", Zero, pure "A") (pure "A")) $
                pure "A"
            )
        )
    it "(\\x => let (a, b) = x in b) :1 (x : (_ :1 A ⨂ A)) -> A   invalid" $
      assertLeft
        (UnusedLinear "a")
        ( doCheckTerm
            [("A", BindingEntry Type)]
            [("A", Zero)]
            (lam "x" $ unpackTensor ("a", "b") (pure "x") (pure "b"))
            ( arr (tensor ("_", One, pure "A") (pure "A")) $
                pure "A"
            )
        )
    it "(\\x => fst x) :1 (x : (A & A)) -o A" $
      assertRight
        ( doCheckTerm
            [("A", BindingEntry Type)]
            [("A", Zero)]
            (lam "x" $ Fst $ pure "x")
            ( limp (with (pure "A") (pure "A")) $
                pure "A"
            )
        )
    it "(\\x => snd x) :1 (x : (A & A)) -o A" $
      assertRight
        ( doCheckTerm
            [("A", BindingEntry Type)]
            [("A", Zero)]
            (lam "x" $ Snd $ pure "x")
            ( limp (with (pure "A") (pure "A")) $
                pure "A"
            )
        )
    it "(\\x => (fst x, snd x)) :1 (x : (A & B)) -o (A & B)" $
      assertRight
        ( doCheckTerm
            [ ("A", BindingEntry Type)
            , ("B", BindingEntry Type)
            ]
            [ ("A", Zero)
            , ("B", Zero)
            ]
            (lam "x" $ MkWith (Fst $ pure "x") (Snd $ pure "x"))
            ( limp (with (pure "A") (pure "B")) $
                with (pure "A") (pure "B")
            )
        )
    it "(\\x => \\y => (fst x, y)) :1 (x : (A & B)) -o B -o (A & B)" $
      assertLeft
        (UnusedLinear "y")
        ( doCheckTerm
            [ ("A", BindingEntry Type)
            , ("B", BindingEntry Type)
            ]
            [ ("A", Zero)
            , ("B", Zero)
            ]
            (lam "x" $ lam "y" $ MkWith (Fst $ pure "x") (pure "y"))
            ( limp (with (pure "A") (pure "B")) $
                limp (pure "B") $
                  with (pure "A") (pure "B")
            )
        )
    it "(\\x => (x, x)) :1 (x : A) -o (A & A)" $
      assertRight
        ( doCheckTerm
            [("A", BindingEntry Type)]
            [("A", Zero)]
            (lam "x" $ MkWith (pure "x") (pure "x"))
            ( limp (pure "A") $
                with (pure "A") (pure "A")
            )
        )
    it "(\\x => let (a, b) = x in (a, b)) :1 (x : (_ : A ⨂ B)) -> (A & B)" $
      {-
      Why? Consumption from each component is not summed when forming a `&`. Each component
      must consume all linear variables. The second component of the tensor is always linear, so it
      must be consumed, but it isn't consumed by the first component of the `&`.
      -}
      assertLeft
        (UnusedLinear "b")
        ( doCheckTerm
            [("A", BindingEntry Type)]
            [("A", Zero)]
            ( lam "x" $
                unpackTensor ("a", "b") (pure "x") $
                  MkWith (pure "a") (pure "b")
            )
            ( arr (tensor ("_", Many, pure "A") (pure "B")) $
                with (pure "A") (pure "B")
            )
        )
    it "(\\x => let (a, b) = x in (a, b)) :1 (x : (_ : A ⨂ B)) -o (A & B)" $
      assertLeft
        (UnusedLinear "b")
        ( doCheckTerm
            [("A", BindingEntry Type)]
            [("A", Zero)]
            ( lam "x" $
                unpackTensor ("a", "b") (pure "x") $
                  MkWith (pure "a") (pure "b")
            )
            ( limp (tensor ("_", Many, pure "A") (pure "B")) $
                with (pure "A") (pure "B")
            )
        )
    it "(\\x => (fst x, snd x)) :1 (x : (A & B)) -> (_ : A ⨂ B)" $
      assertRight
        ( doCheckTerm
            [("A", BindingEntry Type)]
            [("A", Zero)]
            ( lam "x" $
                MkTensor (Fst $ pure "x") (Snd $ pure "x")
            )
            ( arr (with (pure "A") (pure "B")) $
                tensor ("_", Many, pure "A") (pure "B")
            )
        )
    it "(\\x => (fst x, snd x)) :1 (x : (A & B)) -o (_ : A ⨂ B)   invalid" $
      assertLeft
        (OverusedLinear "x")
        ( doCheckTerm
            [("A", BindingEntry Type)]
            [("A", Zero)]
            ( lam "x" $
                MkTensor (Fst $ pure "x") (Snd $ pure "x")
            )
            ( limp (with (pure "A") (pure "B")) $
                tensor ("_", Many, pure "A") (pure "B")
            )
        )
    it "(\\x => \\f => f x) :1 ∀(x : A). (f : A -> B) -> B   invalid" $
      assertLeft
        (UsingErased "x")
        ( doCheckTerm
            [ ("A", BindingEntry Type)
            , ("B", BindingEntry Type)
            ]
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
    it "(\\x => \\f => f x) :1 A -> (b : ∀(a : A). B) -> B" $
      assertRight
        ( doCheckTerm
            [ ("A", BindingEntry Type)
            , ("B", BindingEntry Type)
            ]
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
    it "List : Type -> Type, Nil : ∀(a : Type) -> List a, A :0 Type |- Nil A :1 List A" $ do
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
            [
              ( "List"
              , InductiveEntry
                  (arr Type Type)
                  ( Map.fromList
                      [ ("Nil", nilType)
                      , ("Cons", consType)
                      ]
                  )
              )
            , ("Nil", CtorEntry nilType)
            , ("Cons", CtorEntry consType)
            , ("A", BindingEntry Type)
            ]
            [ ("List", Many)
            , ("Nil", Many)
            , ("Cons", Many)
            , ("A", Zero)
            ]
            (App (pure "Nil") (pure "A"))
            (App (pure "List") (pure "A"))
        )
    it "Bool : Type, True : Bool, False : Bool, x : Bool |- (case x of { True => False; False => True }) :1 Bool" $ do
      let falseType = pure "Bool"
          trueType = pure "Bool"

      assertRight
        ( doCheckTerm
            [
              ( "Bool"
              , InductiveEntry
                  Type
                  ( Map.fromList
                      [ ("False", falseType)
                      , ("True", trueType)
                      ]
                  )
              )
            , ("False", CtorEntry falseType)
            , ("True", CtorEntry trueType)
            , ("x", BindingEntry $ pure "Bool")
            ]
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
    it "A :0 Type, B :0 Type, x : (A & B)  |- (case x of { y => y }) :1 (A & B)" $ do
      assertRight
        ( doCheckTerm
            [ ("A", BindingEntry Type)
            , ("B", BindingEntry Type)
            , ("x", BindingEntry $ with (pure "A") (pure "B"))
            ]
            [ ("A", Zero)
            , ("B", Zero)
            , ("x", Many)
            ]
            ( Case
                (pure "x")
                [ varb "y" $ pure "y"
                ]
            )
            (with (pure "A") (pure "B"))
        )
    it "..., BoolS : Bool -> Type, TrueS : BoolS True, FalseS : BoolS False, b :0 Bool, x : BoolS b  |- (case x of { TrueS => TrueS; FalseS => FalseS }) :1 BoolS b" $ do
      let falseType = pure "Bool"
          trueType = pure "Bool"
          falseSType = App (pure "BoolS") (pure "False")
          trueSType = App (pure "BoolS") (pure "True")

      assertRight
        ( doCheckTerm
            [
              ( "Bool"
              , InductiveEntry
                  Type
                  ( Map.fromList
                      [ ("False", falseType)
                      , ("True", trueType)
                      ]
                  )
              )
            , ("False", CtorEntry falseType)
            , ("True", CtorEntry trueType)
            ,
              ( "BoolS"
              , InductiveEntry
                  (arr (pure "Bool") Type)
                  ( Map.fromList
                      [ ("FalseS", falseSType)
                      , ("TrueS", trueSType)
                      ]
                  )
              )
            , ("FalseS", CtorEntry falseSType)
            , ("TrueS", CtorEntry trueSType)
            , ("b", BindingEntry $ pure "Bool")
            , ("x", BindingEntry $ App (pure "BoolS") (pure "b"))
            ]
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
    it "..., BoolS : Bool -> Type, TrueS : BoolS True, FalseS : BoolS False, b :0 Bool, x : BoolS b  |- (case x of { TrueS => TrueS; FalseS impossible }) :1 BoolS b   invalid" $ do
      let falseType = pure "Bool"
          trueType = pure "Bool"
          falseSType = App (pure "BoolS") (pure "False")
          trueSType = App (pure "BoolS") (pure "True")

      assertLeft
        NotImpossible
        ( doCheckTerm
            [
              ( "Bool"
              , InductiveEntry
                  Type
                  ( Map.fromList
                      [ ("False", falseType)
                      , ("True", trueType)
                      ]
                  )
              )
            , ("False", CtorEntry $ falseType)
            , ("True", CtorEntry $ trueType)
            ,
              ( "BoolS"
              , InductiveEntry
                  (arr (pure "Bool") Type)
                  ( Map.fromList
                      [ ("FalseS", falseSType)
                      , ("TrueS", trueSType)
                      ]
                  )
              )
            , ("FalseS", CtorEntry $ falseSType)
            , ("TrueS", CtorEntry $ trueSType)
            , ("b", BindingEntry $ pure "Bool")
            , ("x", BindingEntry $ App (pure "BoolS") (pure "b"))
            ]
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
                , ctorb_imp "FalseS" []
                ]
            )
            (App (pure "BoolS") (pure "b"))
        )
    it "..., BoolS : Bool -> Type, TrueS : BoolS True, FalseS : BoolS False, b :0 Bool, x : BoolS b  |- (case x of { TrueS => TrueS; FalseS => TrueS }) :1 BoolS b   invalid" $ do
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
            [
              ( "Bool"
              , InductiveEntry
                  Type
                  ( Map.fromList
                      [ ("False", falseType)
                      , ("True", trueType)
                      ]
                  )
              )
            , ("False", CtorEntry $ falseType)
            , ("True", CtorEntry $ trueType)
            ,
              ( "BoolS"
              , InductiveEntry
                  (arr (pure "Bool") Type)
                  ( Map.fromList
                      [ ("FalseS", falseSType)
                      , ("TrueS", trueSType)
                      ]
                  )
              )
            , ("FalseS", CtorEntry falseSType)
            , ("TrueS", CtorEntry trueSType)
            , ("b", BindingEntry $ pure "Bool")
            , ("x", BindingEntry $ App (pure "BoolS") (pure "b"))
            ]
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
    it "..., BoolS : Bool -> Type, TrueS : BoolS True, FalseS : BoolS False, x : BoolS True  |- (case x of { TrueS => TrueS; FalseS impossible }) :1 BoolS b" $ do
      let falseType = pure "Bool"
          trueType = pure "Bool"
          falseSType = App (pure "BoolS") (pure "False")
          trueSType = App (pure "BoolS") (pure "True")

      assertRight
        ( doCheckTerm
            [
              ( "Bool"
              , InductiveEntry
                  Type
                  ( Map.fromList
                      [ ("False", falseType)
                      , ("True", trueType)
                      ]
                  )
              )
            , ("False", CtorEntry falseType)
            , ("True", CtorEntry trueType)
            ,
              ( "BoolS"
              , InductiveEntry
                  (arr (pure "Bool") Type)
                  ( Map.fromList
                      [ ("FalseS", falseSType)
                      , ("TrueS", trueSType)
                      ]
                  )
              )
            , ("FalseS", CtorEntry falseSType)
            , ("TrueS", CtorEntry trueSType)
            , ("x", BindingEntry $ App (pure "BoolS") (pure "True"))
            ]
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
    it "Pair : Type -> Type -> Type, MkPair : (A : Type) -> (B : Type) -> (x : A) -> (y : B) -> Pair A B, A :0 Type, B :0 Type, x :1 Pair A B  |- (case x of { MkPair A B a b => a }) :1 A" $ do
      let mkPairType =
            forall_ ("A", Type) $
              forall_ ("B", Type) $
                pi ("x", pure "A") $
                  pi ("y", pure "B") $
                    App (App (pure "Pair") (pure "A")) (pure "B")

      assertRight
        ( doCheckTerm
            [
              ( "Pair"
              , InductiveEntry
                  (arr Type $ arr Type Type)
                  ( Map.fromList
                      [ ("MkPair", mkPairType)
                      ]
                  )
              )
            , ("MkPair", CtorEntry mkPairType)
            , ("A", BindingEntry Type)
            , ("B", BindingEntry Type)
            , ("x", BindingEntry $ App (App (pure "Pair") (pure "A")) (pure "B"))
            ]
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
    it "Pair : Type -> Type -> Type, MkPair : (A : Type) -> (B : Type) -> (x : A) -o (y : B) -o Pair A B, A :0 Type, B :0 Type, x :1 Pair A B  |- (case x of { MkPair A B a b => a }) :1 A   invalid" $ do
      let mkPairType =
            forall_ ("A", Type) $
              forall_ ("B", Type) $
                limp (pure "A") $
                  limp (pure "B") $
                    App (App (pure "Pair") (pure "A")) (pure "B")

      assertLeft
        (UnusedLinear "y")
        ( doCheckTerm
            [
              ( "Pair"
              , InductiveEntry
                  (arr Type $ arr Type Type)
                  ( Map.fromList
                      [ ("MkPair", mkPairType)
                      ]
                  )
              )
            , ("MkPair", CtorEntry mkPairType)
            , ("A", BindingEntry Type)
            , ("B", BindingEntry Type)
            , ("x", BindingEntry $ App (App (pure "Pair") (pure "A")) (pure "B"))
            ]
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
    it "Pair : Type -> Type -> Type, MkPair : (A : Type) -> (B : Type) -> (x : A) -> (y : B) -> Pair A B, A :0 Type, B :0 Type, a :1 A, b :1 B  |- MkPair A B a b :1 Pair A B   invalid" $ do
      let mkPairType =
            forall_ ("A", Type) $
              forall_ ("B", Type) $
                pi ("x", pure "A") $
                  pi ("y", pure "B") $
                    App (App (pure "Pair") (pure "A")) (pure "B")

      assertLeft
        (OverusedLinear "a")
        ( doCheckTerm
            [
              ( "Pair"
              , InductiveEntry
                  (arr Type $ arr Type Type)
                  ( Map.fromList
                      [ ("MkPair", mkPairType)
                      ]
                  )
              )
            , ("MkPair", CtorEntry mkPairType)
            , ("A", BindingEntry Type)
            , ("B", BindingEntry Type)
            , ("a", BindingEntry $ pure "A")
            , ("b", BindingEntry $ pure "B")
            ]
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
    it "Pair : Type -> Type -> Type, MkPair : (A :0 Type) -> (B :0 Type) -> (x : A) -> (y : B) -> Pair A B, A :0 Type, B :0 Type, x :1 Pair A B  |- (case x of { MkPair A B a b => A }) :1 Type   invalid" $ do
      let mkPairType =
            forall_ ("A", Type) $
              forall_ ("B", Type) $
                pi ("x", pure "A") $
                  pi ("y", pure "B") $
                    App (App (pure "Pair") (pure "A")) (pure "B")

      assertLeft
        (UsingErased "A")
        ( doCheckTerm
            [
              ( "Pair"
              , InductiveEntry
                  (arr Type $ arr Type Type)
                  ( Map.fromList
                      [ ("MkPair", mkPairType)
                      ]
                  )
              )
            , ("MkPair", CtorEntry mkPairType)
            , ("A", BindingEntry Type)
            , ("B", BindingEntry Type)
            , ("x", BindingEntry $ App (App (pure "Pair") (pure "A")) (pure "B"))
            ]
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
    it "Pair : Type -> Type -> Type, MkPair : (A : Type) -> (B : Type) -> (x : A) -> (y : B) -> Pair A B, A :0 Type, B :0 Type, x :w Pair A B  |- (case x of { MkPair A B a b => a }) :1 A" $ do
      let mkPairType =
            forall_ ("A", Type) $
              forall_ ("B", Type) $
                pi ("x", pure "A") $
                  pi ("y", pure "B") $
                    App (App (pure "Pair") (pure "A")) (pure "B")

      assertRight
        ( doCheckTerm
            [
              ( "Pair"
              , InductiveEntry
                  (arr Type $ arr Type Type)
                  ( Map.fromList
                      [ ("MkPair", mkPairType)
                      ]
                  )
              )
            , ("MkPair", CtorEntry mkPairType)
            , ("A", BindingEntry Type)
            , ("B", BindingEntry Type)
            , ("x", BindingEntry $ App (App (pure "Pair") (pure "A")) (pure "B"))
            ]
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
