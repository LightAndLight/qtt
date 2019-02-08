{-# language OverloadedLists #-}
{-# language TypeApplications #-}
module Test.Pretty where

import Text.PrettyPrint.ANSI.Leijen (Doc)
import Test.Hspec

import Syntax
import Syntax.Pretty

pretty1 :: Doc
pretty1 = prettyTerm @String @String (Case (pure "a") [varb "x" $ pure "x"])

pretty2 :: Doc
pretty2 =
  prettyTerm @String @String $
  Case (pure "a")
  [ varb "x" $ pure "x"
  , varb "y" $ pure "y"
  ]

pretty3 :: Doc
pretty3 =
  prettyTerm @String @String $
  Case (pure "a")
  [ ctorb "Nil" [] $ pure "Nil"
  , ctorb "Cons" ["a", "b"] $ App (App (pure "Cons") (pure "a")) (pure "b")
  ]

pretty4 :: Doc
pretty4 =
  prettyTerm @String @String $
  Case (pure "a")
  [ ctorb "Nil" [] $ pure "Nil"
  , ctorb "Cons" ["a", "b"] $
    Case (pure "b")
    [ ctorb "Nil" [] $ pure "Nil"
    , ctorb "Cons" ["a", "b"] $ App (App (pure "Cons") (pure "a")) (pure "b")
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
