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
doUnify = unifyTerms id (const Nothing)

unifySpec :: Spec
unifySpec =
  describe "unify" $ do
    it "(\\x => x) ~ (\\x -> x)  succeeds with {}" $
      doUnify (lam "x" $ pure "x") (lam "x" $ pure "x") `shouldBe`
      Right mempty
    it "(\\x => x) ~ (\\x -> y)  fails" $
      doUnify (lam "x" $ pure "x") (lam "x" $ pure "y") `shouldBe`
      Left (TypeMismatch (Var "x") (Var "y"))
    it "(x : A) -> f x ~ (x : A) -> f x  succeeds with {}" $
      doUnify
        (pi ("x", pure "A") (App (pure "f") (pure "x")))
        (pi ("x", pure "A") (App (pure "f") (pure "x")))
        `shouldBe` Right mempty
    it "(\\x => x) ~ (\\x -> (y, z))  fails" $
      doUnify (lam "x" $ pure "x") (lam "x" $ MkTensor (pure "y") (pure "z"))
      `shouldBe` Left (TypeMismatch (Var "x") (MkTensor (pure "y") (pure "z")))
    it "(\\x => x) ~ (\\x -> Unit)  fails" $
      doUnify (lam "x" $ pure "x") (lam "x" $ MkUnit)
      `shouldBe` Left (TypeMismatch (Var "x") MkUnit)
    it "(\\x => a) ~ (\\x -> (b, c))  succeeds with {a -> (b, c)}" $
      doUnify (lam "x" $ pure "a") (lam "x" $ MkTensor (pure "b") (pure "c"))
      `shouldBe`
      Right (Subst $ Map.fromList [("a", MkTensor (pure "b") (pure "c"))])
