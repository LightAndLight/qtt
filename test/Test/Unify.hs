module Test.Unify (unifySpec) where

import Prelude hiding (pi)

import Test.Hspec

import qualified Data.Map as Map

import Syntax
import Unify

doUnify ::
  Term String String String ->
  Term String String String ->
  Maybe (Subst (Term String String) String)
doUnify = unifyTerms (const Nothing)

unifySpec :: Spec
unifySpec =
  describe "unify" $ do
    it "(\\x => x) ~ (\\x -> x)  succeeds with {}" $
      doUnify (lam "x" $ pure "x") (lam "x" $ pure "x") `shouldBe`
      Just mempty
    it "(\\x => x) ~ (\\x -> y)  fails" $
      doUnify (lam "x" $ pure "x") (lam "x" $ pure "y") `shouldBe`
      Nothing
    it "(x : A) -> f x ~ (x : A) -> f x  succeeds with {}" $
      doUnify
        (pi ("x", pure "A") (App (pure "f") (pure "x")))
        (pi ("x", pure "A") (App (pure "f") (pure "x")))
        `shouldBe` Just mempty
    it "(\\x => x) ~ (\\x -> (y, z))  fails" $
      doUnify (lam "x" $ pure "x") (lam "x" $ MkTensor (pure "y") (pure "z"))
      `shouldBe` Nothing
    it "(\\x => x) ~ (\\x -> Unit)  fails" $
      doUnify (lam "x" $ pure "x") (lam "x" $ MkUnit)
      `shouldBe` Nothing
    it "(\\x => a) ~ (\\x -> (b, c))  succeeds with {a -> (b, c)}" $
      doUnify (lam "x" $ pure "a") (lam "x" $ MkTensor (pure "b") (pure "c"))
      `shouldBe`
      Just (Subst $ Map.fromList [("a", MkTensor (pure "b") (pure "c"))])
