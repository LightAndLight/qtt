{-# language OverloadedLists #-}
module Test.Extract where

import Prelude hiding (pi)

import Data.Map (Map)
import Test.Hspec
import Text.PrettyPrint.ANSI.Leijen (Doc, pretty)

import qualified Data.Map as Map

import Context
import Extract
import Inductive
import Syntax
import Typecheck

doPrettyHs :: HsTm String -> Doc
doPrettyHs = pretty

doExtractTerm ::
  Map String (Usage, Entry String String String) ->
  Term String String String ->
  Ty String String String ->
  Expectation
doExtractTerm env tm ty =
  either (expectationFailure . show) (print . pretty) mtm
  where
    mtm =
      extractTerm
        HsTyVar
        (toEnv env)
        tm
        Many
        ty

doExtractInductive ::
  Show l =>
  Map String (Usage, Entry String l String) ->
  Inductive String l String ->
  Expectation
doExtractInductive env ind =
  either
    (expectationFailure . show)
    (print . pretty)
    (extractInductive (toEnv env) ind)

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

listInd :: Inductive String String String
listInd =
  Inductive
  { _indTypeName = "List"
  , _indTypeType = arr Type Type
  , _indConstructors =
    Map.fromList
    [ ("Nil", forall_ ("a", Type) $ App (pure "List") (pure "a"))
    , ( "Cons"
      , forall_ ("a", Type) $
        arr (pure "a") $
        arr (App (pure "List") (pure "a")) $
        App (pure "List") (pure "a")
      )
    ]
  }

natInd :: Inductive String String String
natInd =
  Inductive
  { _indTypeName = "Nat"
  , _indTypeType = Type
  , _indConstructors =
    Map.fromList
    [ ("Z", pure "Nat")
    , ("S", arr (pure "Nat") $ pure "Nat")
    ]
  }

vectInd :: Inductive String String String
vectInd =
  Inductive
  { _indTypeName = "Vect"
  , _indTypeType = arr (pure "Nat") (arr Type Type)
  , _indConstructors =
    Map.fromList
    [ ( "Nil"
      , forall_ ("a", Type) $
        App (App (pure "Vect") (pure "Z")) (pure "a")
      )
    , ( "Cons"
      , forall_ ("n", pure "Nat") $
        forall_ ("a", Type) $
        arr (pure "a") $
        arr (App (App (pure "Vect") (pure "n")) (pure "a")) $
        App (App (pure "Vect") (App (pure "S") (pure "n"))) (pure "a")
      )
    ]
  }

subsetInd :: Inductive String String String
subsetInd =
  Inductive
  { _indTypeName = "Subset"
  , _indTypeType =
    forall_ ("a", Type) $
    arr (arr (pure "a") Type) $
    Type
  , _indConstructors =
    Map.fromList
    [ ( "MkSubset"
      , forall_ ("a", Type) $
        forall_ ("p", arr (pure "a") Type) $
        pi ("x", pure "a") $
        forall_ ("ev", App (pure "p") (pure "a")) $
        App (App (pure "Subset") (pure "a")) (pure "p")
      )
    ]
  }

caseSubsetTy :: Term String String String
caseSubsetTy =
  forall_ ("a", Type) $
  forall_ ("p", arr (pure "a") Type) $
  arr (App (App (pure "Subset") (pure "a")) (pure "p")) $
  pure "a"

caseSubsetTm :: Term String String String
caseSubsetTm =
  lam "a" $
  lam "p" $
  lam "x" $
  Case (pure "x")
  [ ctorb "MkSubset" ["a", "p", "x", "ev"] $
    pure "x"
  ]

extractSpec :: Spec
extractSpec =
  describe "extraction" $ do
    it "const" $
      doExtractTerm mempty constTm constTy
    it "const eta 1" $
      doExtractTerm mempty (lam "A" $ App (Ann constTm Many constTy) (pure "A")) constTy
    it "fst" $
      doExtractTerm mempty fstTm fstTy
    it "idf" $
      doExtractTerm mempty idfTm idfTy
    it "list" $
      doExtractInductive mempty listInd
    it "vect" $
      doExtractInductive (inductiveEntry natInd) vectInd
    it "subset" $
      doExtractInductive mempty subsetInd
    it "subset case" $
      doExtractTerm (inductiveEntry subsetInd) caseSubsetTm caseSubsetTy
