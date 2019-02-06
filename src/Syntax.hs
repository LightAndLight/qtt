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
data Term a
  = Var a
  | Ann (Term a) Usage (Term a)
  | Type

  | Lam (Scope () Term a)
  | Pi Usage (Term a) (Scope () Term a)
  | App (Term a) (Term a)

  | MkTensor (Term a) (Term a)
  | Tensor (Term a) (Scope () Term a)
  | UnpackTensor (Term a) (Scope Bool Term a)

  | MkWith (Term a) (Term a)
  | With (Term a) (Scope () Term a)
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

arr :: Term a -> Term a -> Term a
arr a b = Pi Many a $ lift b

limp :: Term a -> Term a -> Term a
limp a b = Pi One a $ lift b

unpackTensor :: Eq a => (a, a) -> Term a -> Term a -> Term a
unpackTensor (x, y) m n =
  UnpackTensor m $
  abstract
    (\z -> if z == x then Just False else if z == y then Just True else Nothing)
    n

deriving instance Eq a => Eq (Term a)
deriving instance Show a => Show (Term a)
