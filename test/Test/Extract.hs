module Test.Extract where

import Prelude hiding (pi)

import Test.Hspec
import Text.PrettyPrint.ANSI.Leijen (Doc, pretty)

import Extract
import Syntax
import Typecheck

doPrettyHs :: HsTm String -> Doc
doPrettyHs = pretty

doExtractTerm ::
  Ord a =>
  Term a l a ->
  Ty a l a ->
  Maybe (HsTm a)
doExtractTerm tm =
  extractTerm
    (Env id id (const Nothing) (const Nothing))
    tm
    Many

constTy :: Term String String String
constTy =
  forall_ ("A", Type) $
  forall_ ("B", Type) $
  pi ("x", pure "A") $
  pi ("y", pure "B") $
  pure "A"

constTm :: Term String String String
constTm =
  lam "A" $ lam "B" $
  lam "x" $ lam "y" $
  pure "x"

extractSpec :: Spec
extractSpec =
  describe "extraction" $ do
    it "const" $ do
      print . maybe mempty pretty $ doExtractTerm constTm constTy
    it "const eta 1" $ do
      print . maybe mempty pretty $
        doExtractTerm (lam "A" $ App (Ann constTm Many constTy) (pure "A")) constTy