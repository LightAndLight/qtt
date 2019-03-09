module Test.Extract where

import Prelude hiding (pi)

import Test.Hspec
import Text.PrettyPrint.ANSI.Leijen (Pretty, Doc, pretty)

import Extract
import Syntax
import Typecheck

doPrettyHs :: HsTm String -> Doc
doPrettyHs = pretty

doExtractTerm ::
  (Ord a, Pretty a) =>
  Term a l a ->
  Ty a l a ->
  Expectation
doExtractTerm tm ty =
  maybe (expectationFailure "extract term Nothing") (print . pretty) mtm
  where
    mtm =
      extractTerm
        HsTyVar
        (Env id id (const Nothing) (const Nothing))
        tm
        Many
        ty

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

fstTy :: Term String String String
fstTy =
  forall_ ("A", Type) $
  forall_ ("B", Type) $
  arr (tensor ("_", pure "A") (pure "B")) $
  pure "A"

fstTm :: Term String String String
fstTm =
  lam "A" $ lam "B" $
  lam "x" $ unpackTensor ("a", "b") (pure "x") $
  pure "a"

idfTy :: Term String String String
idfTy =
  forall_ ("F", arr Type Type) $
  forall_ ("A", Type) $
  pi ("x", App (pure "F") (pure "A")) $
  App (pure "F") (pure "A")

idfTm :: Term String String String
idfTm =
  lam "F" $ lam "A" $
  lam "x" $
  pure "x"

extractSpec :: Spec
extractSpec =
  describe "extraction" $ do
    it "const" $
      doExtractTerm constTm constTy
    it "const eta 1" $
      doExtractTerm (lam "A" $ App (Ann constTm Many constTy) (pure "A")) constTy
    it "fst" $
      doExtractTerm fstTm fstTy
    it "idf" $
      doExtractTerm idfTm idfTy
