{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# language StandaloneDeriving #-}
{-# language TemplateHaskell #-}
module Syntax where

import Bound.Scope (Scope)
import Bound.TH (makeBound)
import Data.Deriving (deriveEq1, deriveShow1)

import Data.Semiring (Semiring(..))

data Usage = Zero | One | Many
  deriving (Eq, Show)

instance Semiring Usage where
  zero = Zero
  one = One

  plus Zero m = m
  plus One Zero = One
  plus One One = Many
  plus One Many = Many
  plus Many m = Many

  times Zero m = Zero
  times One m = m
  times Many Zero = Zero
  times Many One = Many
  times Many Many = Many

type Ty = Term
data Term a
  = Var a
  | Ann (Term a) Usage (Term a)
  | Type
  | Lam (Scope () Term a)
  | Pi Usage (Term a) (Scope () Term a)
  | App (Term a) (Term a)
  | Pair (Term a) (Term a)
  | Sigma Usage (Term a) (Scope () Term a)
  | Fst (Term a)
  | Snd (Term a)
  deriving (Functor, Foldable, Traversable)
makeBound ''Term
deriveEq1 ''Term
deriveShow1 ''Term

deriving instance Eq a => Eq (Term a)
deriving instance Show a => Show (Term a)
