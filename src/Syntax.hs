{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# language StandaloneDeriving #-}
{-# language TemplateHaskell #-}
module Syntax where

import Bound.Name (Name(..), abstractName, abstract1Name)
import Bound.Scope (Scope)
import Bound.TH (makeBound)
import Control.Monad.Trans.Class (lift)
import Data.Deriving (deriveShow1)
import Data.Functor.Classes (Eq1(..), eq1, showsPrec1)
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
data Term n l a
  = Var a
  | Ann (Term n l a) Usage (Term n l a)
  | Type

  | Lam n (Scope (Name n ()) (Term n l) a)
  | Pi Usage (Maybe n) (Term n l a) (Scope (Name n ()) (Term n l) a)
  | App (Term n l a) (Term n l a)

  | MkTensor (Term n l a) (Term n l a)
  | Tensor n (Term n l a) (Scope (Name n ()) (Term n l) a)
  | UnpackTensor n n (Term n l a) (Scope (Name n Bool) (Term n l) a)

  | MkWith (Term n l a) (Term n l a)
  | With n (Term n l a) (Scope (Name n ()) (Term n l) a)
  | Fst (Term n l a)
  | Snd (Term n l a)

  | Unit
  | MkUnit

  | Loc l (Term n l a)
  deriving (Functor, Foldable, Traversable)
makeBound ''Term
deriveShow1 ''Term

instance (Show n, Show l, Show a) => Show (Term n l a) where
  showsPrec = showsPrec1

instance Eq1 (Term n l) where
  liftEq _ Type Type = True
  liftEq f (Var a) (Var a') = f a a'
  liftEq f (Ann a b c) (Ann a' b' c') =
    liftEq f a a' && b == b' && liftEq f c c'
  liftEq f (Lam _ a) (Lam _ a') = liftEq f a a'
  liftEq f (Pi a _ b c) (Pi a' _ b' c') =
    a == a' && liftEq f b b' && liftEq f c c'
  liftEq f (App a b) (App a' b') = liftEq f a a' && liftEq f b b'
  liftEq f (MkTensor a b) (MkTensor a' b') = liftEq f a a' && liftEq f b b'
  liftEq f (Tensor _ a b) (Tensor _ a' b') = liftEq f a a' && liftEq f b b'
  liftEq f (UnpackTensor _ _ a b) (UnpackTensor _ _ a' b') =
    liftEq f a a' && liftEq f b b'
  liftEq f (MkWith a b) (MkWith a' b') = liftEq f a a' && liftEq f b b'
  liftEq f (With _ a b) (With _ a' b') = liftEq f a a' && liftEq f b b'
  liftEq f (Fst a) (Fst a') = liftEq f a a'
  liftEq f (Snd a) (Snd a') = liftEq f a a'
  liftEq _ Unit Unit = True
  liftEq _ MkUnit MkUnit = True
  liftEq f (Loc _ a) b = liftEq f a b
  liftEq f a (Loc _ b) = liftEq f a b
  liftEq _ _ _ = False

instance Eq a => Eq (Term n l a) where
  (==) = eq1

lam :: Eq a => a -> Term a l a -> Term a l a
lam a = Lam a . abstract1Name a

pi :: Eq a => (a, Ty a l a) -> Term a l a -> Term a l a
pi (a, ty) = Pi Many (Just a) ty . abstract1Name a

lpi :: Eq a => (a, Ty a l a) -> Term a l a -> Term a l a
lpi (a, ty) = Pi One (Just a) ty . abstract1Name a

forall_ :: Eq a => (a, Ty a l a) -> Term a l a -> Term a l a
forall_ (a, ty) = Pi Zero (Just a) ty . abstract1Name a

arr :: Term n l a -> Term n l a -> Term n l a
arr a b = Pi Many Nothing a $ lift b

limp :: Term n l a -> Term n l a -> Term n l a
limp a b = Pi One Nothing a $ lift b

tensor :: Eq a => (a, Ty a l a) -> Ty a l a -> Ty a l a
tensor (a, ty) = Tensor a ty . abstract1Name a

with :: Eq a => (a, Ty a l a) -> Ty a l a -> Ty a l a
with (a, ty) = With a ty . abstract1Name a

unpackTensor :: Eq a => (a, a) -> Term a l a -> Term a l a -> Term a l a
unpackTensor (x, y) m n =
  UnpackTensor x y m $
  abstractName
    (\z ->
       if z == x
       then Just False
       else if z == y then Just True else Nothing)
    n