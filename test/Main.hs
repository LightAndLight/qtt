{-# language LambdaCase #-}
{-# language TypeApplications #-}
module Main where

import Test.Hspec

import Test.Extract
import Test.Pretty
import Test.Typecheck
import Test.Unify

main :: IO ()
main =
  hspec $ do
    prettySpec
    typecheckSpec
    unifySpec
    extractSpec