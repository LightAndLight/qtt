{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# language StandaloneDeriving #-}
{-# language TemplateHaskell #-}
module Syntax where

import Bound.Scope (Scope, abstract1, abstract)
import Bound.TH (makeBound)
import Control.Monad.Trans.Class (lift)
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

instance Semiring Usage where
  zero = Zero

  plus Zero m = m
  plus One Zero = One
  plus One One = Many
  plus One Many = Many
  plus Many _ = Many

{-   maybe the semiring is wrong?
  one = One

  times Zero _ = Zero
  times One m = m
  times Many Zero = Zero
  times Many One = Many
  times Many Many = Many
-}

  one = Many

  times Zero _ = Zero
  times One Zero = Zero
  times One One = One
  times One Many = One
  times Many m = m

type Ty = Term
data Term l a
  = Var a
  | Ann (Term l a) Usage (Term l a)
  | Type

  | Lam (Scope () (Term l) a)
  | Pi Usage (Term l a) (Scope () (Term l) a)
  | App (Term l a) (Term l a)

  | MkTensor (Term l a) (Term l a)
  | Tensor (Term l a) (Scope () (Term l) a)
  | UnpackTensor (Term l a) (Scope Bool (Term l) a)

  | MkWith (Term l a) (Term l a)
  | With (Term l a) (Scope () (Term l) a)
  | Fst (Term l a)
  | Snd (Term l a)

  | Unit
  | MkUnit

  | Loc l (Term l a)
  deriving (Functor, Foldable, Traversable)
makeBound ''Term
deriveEq1 ''Term
deriveShow1 ''Term

lam :: Eq a => a -> Term l a -> Term l a
lam a = Lam . abstract1 a

pi :: Eq a => (a, Ty l a) -> Term l a -> Term l a
pi (a, ty) = Pi Many ty . abstract1 a

lpi :: Eq a => (a, Ty l a) -> Term l a -> Term l a
lpi (a, ty) = Pi One ty . abstract1 a

forall_ :: Eq a => (a, Ty l a) -> Term l a -> Term l a
forall_ (a, ty) = Pi Zero ty . abstract1 a

arr :: Term l a -> Term l a -> Term l a
arr a b = Pi Many a $ lift b

limp :: Term l a -> Term l a -> Term l a
limp a b = Pi One a $ lift b

unpackTensor :: Eq a => (a, a) -> Term l a -> Term l a -> Term l a
unpackTensor (x, y) m n =
  UnpackTensor m $
  abstract
    (\z -> if z == x then Just False else if z == y then Just True else Nothing)
    n

deriving instance (Eq l, Eq a) => Eq (Term l a)
deriving instance (Show l, Show a) => Show (Term l a)