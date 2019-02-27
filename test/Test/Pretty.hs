{-# language OverloadedLists #-}
module Test.Pretty where

import Text.PrettyPrint.ANSI.Leijen (Doc, pretty)
import Test.Hspec

import Syntax
import Syntax.Pretty

doPrettyTerm :: Term String String String -> Doc
doPrettyTerm = prettyTerm pretty

pretty1 :: Doc
pretty1 = doPrettyTerm $ Case (pure "a") [varb "x" $ pure "x"]

pretty2 :: Doc
pretty2 =
  doPrettyTerm $
  Case (pure "a")
  [ varb "x" $ pure "x"
  , varb "y" $ pure "y"
  ]

pretty3 :: Doc
pretty3 =
  doPrettyTerm $
  Case (pure "a")
  [ ctorb "Nil" [] $ pure "Nil"
  , ctorb "Cons" ["a", "b"] $ App (App (pure "Cons") (pure "a")) (pure "b")
  ]

pretty4 :: Doc
pretty4 =
  doPrettyTerm $
  Case (pure "a")
  [ ctorb "Nil" [] $ pure "Nil"
  , ctorb "Cons" ["a", "b"] $
    Case (pure "b")
    [ ctorb "Nil" [] $ pure "Nil"
    , ctorb "Cons" ["c", "d"] $ App (App (pure "Cons") (pure "c")) (pure "d")
    ]
  ]

prettySpec :: Spec
prettySpec =
  describe "pretty" $ do
    it "1" $ do
      putStrLn $ show pretty1
    it "2" $ do
      putStrLn $ show pretty2
    it "3" $ do
      putStrLn $ show pretty3
    it "4" $ do
      putStrLn $ show pretty4
