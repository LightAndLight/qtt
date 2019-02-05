{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# language StandaloneDeriving #-}
{-# language TemplateHaskell #-}
module Syntax where

import Bound.Scope (Scope, abstract1)
import Bound.TH (makeBound)
import Data.Deriving (deriveEq1, deriveShow1)
import Data.Semiring (Semiring(..))
import Text.PrettyPrint.ANSI.Leijen (Pretty(..))

import qualified Text.PrettyPrint.ANSI.Leijen as Pretty

data Usage = Zero | One | Many
  deriving (Eq, Show)

instance Pretty Usage where
  pretty Zero = Pretty.char '0'
  pretty One = Pretty.char '1'
  pretty Many = Pretty.char 'w'

weaken :: Usage -> Usage
weaken Many = One
weaken a = a

instance Semiring Usage where
  zero = Zero
  one = One

  plus Zero m = m
  plus One Zero = One
  plus One One = Many
  plus One Many = Many
  plus Many _ = Many

  times Zero _ = Zero
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
  | UnpackSigma (Term a) (Scope Bool Term a)
  | Fst (Term a)
  | Snd (Term a)
  | Unit
  | MkUnit
  deriving (Functor, Foldable, Traversable)
makeBound ''Term
deriveEq1 ''Term
deriveShow1 ''Term

lam :: Eq a => a -> Term a -> Term a
lam a = Lam . abstract1 a

pi :: Eq a => (a, Usage, Ty a) -> Term a -> Term a
pi (a, u, ty) = Pi u ty . abstract1 a

deriving instance Eq a => Eq (Term a)
deriving instance Show a => Show (Term a)
