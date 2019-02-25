module TypeError where

import Data.Set (Set)

import Syntax

data TypeError l a
  = NotInScope a
  | UsingErased a
  | UnusedLinear a
  | ExpectedType (Term a l a)
  | ExpectedPi (Term a l a)
  | ExpectedTensor (Term a l a)
  | ExpectedWith (Term a l a)
  | ExpectedUnit (Term a l a)
  | TypeMismatch (Term a l a) (Term a l a)
  | Can'tInfer (Term a l a)
  | NotConstructorFor a (Term a l a)
  | TooManyArguments a
  | NotEnoughArguments a
  | NotImpossible
  | UnmatchedCases (Set a)
  | UnknownSolution (Term a l a) (Term a l a)
  deriving (Eq, Show)
