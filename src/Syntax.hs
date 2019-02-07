{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# language ExistentialQuantification #-}
{-# language GADTs #-}
{-# language StandaloneDeriving #-}
{-# language TemplateHaskell #-}
module Syntax where

import Bound.Class ((>>>=))
import Bound.Scope (Scope, abstract1, abstract)
import Bound.TH (makeBound)
import Control.Monad.Trans.Class (lift)
import Data.Deriving (deriveEq1, deriveShow1)
import Data.Semiring (Semiring(..))
import Data.Void (Void)
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

data Pattern p where
  PVar :: Pattern ()
  PCtor :: String -> Int -> Pattern Int
  PWild :: Pattern Void
deriving instance Eq (Pattern p)
deriving instance Show (Pattern p)

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

  | forall p. Case (Term a) [(Pattern p, Scope p Term a)]
deriving instance Functor Term
deriving instance Foldable Term
deriving instance Traversable Term
deriveEq1 ''Term
deriveShow1 ''Term

instance Applicative Term where; pure = return; (<*>) = ap
instance Monad Term where
  return = Var

  tm >>= f =
    case tm of
      Var a -> f a
      Ann a b c -> Ann (a >>= f) b (c >>= f)
      Type -> Type

      Lam a -> Lam (a >>>= f)
      Pi a b c -> Pi a (b >>= f) (c >>>= f)
      App a b -> App (a >>= f) (b >>= f)

      MkTensor a b -> MkTensor (a >>= f) (b >>= f)
      Tensor a b -> Tensor (a >>= f) (b >>>= f)
      UnpackTensor a b -> UnpackTensor (a >>= f) (b >>>= f)

      MkWith a b -> MkWith (a >>= f) (b >>= f)
      With a b -> With (a >>= f) (b >>>= f)
      Fst a -> Fst (a >>= f)
      Snd a -> Snd (a >>= f)

      Unit -> Unit
      MkUnit -> MkUnit

      Case a b -> Case (a >>= f) (fmap (fmap (>>>= f)) b)

lam :: Eq a => a -> Term a -> Term a
lam a = Lam . abstract1 a

pi :: Eq a => (a, Ty a) -> Term a -> Term a
pi (a, ty) = Pi Many ty . abstract1 a

lpi :: Eq a => (a, Ty a) -> Term a -> Term a
lpi (a, ty) = Pi One ty . abstract1 a

forall_ :: Eq a => (a, Ty a) -> Term a -> Term a
forall_ (a, ty) = Pi Zero ty . abstract1 a

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