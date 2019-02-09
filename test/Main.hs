{-# language LambdaCase #-}
{-# language TypeApplications #-}
module Main where

import Test.Hspec

import Test.Pretty
import Test.Typecheck

main :: IO ()
main =
  hspec $ do
    prettySpec
    typecheckSpec