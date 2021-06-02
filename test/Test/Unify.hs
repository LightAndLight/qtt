module Test.Unify (unifySpec) where

import Prelude hiding (pi)

import Test.Hspec

import qualified Data.Map as Map

import Syntax
import TypeError
import Unify

doUnify ::
  Term String String String ->
  Term String String String ->
  Either
    (TypeError String String)
    (Subst (Term String String) String)
doUnify = unifyTerms id id (const Nothing)

unifySpec :: Spec
unifySpec =
  describe "unify" $ do
    it "(\\x => x) ~ (\\x -> x)  succeeds with {}" $
      doUnify (lam "x" $ pure "x") (lam "x" $ pure "x")
        `shouldBe` Right mempty
    it "(\\x => x) ~ (\\x -> y)  fails" $
      doUnify (lam "x" $ pure "x") (lam "x" $ pure "y")
        `shouldBe` Left (TypeMismatch (Var "x") (Var "y"))
    it "(\\x => x) ~ (\\x -> (y, z))  fails" $
      doUnify (lam "x" $ pure "x") (lam "x" $ MkTensor (pure "y") (pure "z"))
        `shouldBe` Left (TypeMismatch (Var "x") (MkTensor (pure "y") (pure "z")))
    it "(\\x => x) ~ (\\x -> MkUnit)  fails" $
      doUnify (lam "x" $ pure "x") (lam "x" $ MkUnit)
        `shouldBe` Left (TypeMismatch (Var "x") MkUnit)
    it "(\\x => a) ~ (\\x -> (b, c))  succeeds with {a -> (b, c)}" $
      doUnify (lam "x" $ pure "a") (lam "x" $ MkTensor (pure "b") (pure "c"))
        `shouldBe` Right (Subst $ Map.fromList [("a", MkTensor (pure "b") (pure "c"))])
    it "f x ~ Unit  fails" $
      doUnify (App (pure "f") (pure "x")) MkUnit
        `shouldBe` Left (UnknownSolution (App (pure "f") (pure "x")) MkUnit)
    it "(a, b) ~ (c, d)  succeeds with {a -> c, b -> d}" $
      doUnify
        (MkTensor (pure "a") (pure "b"))
        (MkTensor (pure "c") (pure "d"))
        `shouldBe` Right (Subst $ Map.fromList [("a", pure "c"), ("b", pure "d")])
