{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}

module Syntax where

import Bound.Class (Bound (..))
import Bound.Scope (Scope, abstract, abstract1)
import Control.Monad (ap)
import Control.Monad.Trans.Class (lift)
import Data.Deriving (deriveShow1)
import Data.Functor.Classes (Eq1 (..), Show1 (..), eq1, showsPrec1)
import Data.List (elemIndex)
import Data.List.NonEmpty (NonEmpty)
import Data.Maybe (isJust)
import Data.Semiring (Semiring (..))
import Data.Type.Equality ((:~:) (..))
import GHC.Exts (IsString)
import Text.PrettyPrint.ANSI.Leijen (Pretty (..))

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

  one = One

  times Zero _ = Zero
  times One m = m
  times Many Zero = Zero
  times Many One = Many
  times Many Many = Many

data Pattern c p where
  PVar :: c -> Pattern c ()
  PCtor :: c -> [c] -> Int -> Pattern c Int
deriving instance Show c => Show (Pattern c p)

eqPattern :: Eq c => Pattern c p -> Pattern c p' -> Maybe (p :~: p')
eqPattern (PVar _) (PVar _) = Just Refl
eqPattern (PCtor a _ b) (PCtor a' _ b') | a == a', b == b' = Just Refl
eqPattern _ _ = Nothing

data Path p where
  V :: Path ()
  C :: Int -> Path Int
deriving instance Eq (Path p)
deriving instance Ord (Path p)
deriving instance Show (Path p)

pathVal :: Path p -> p
pathVal V = ()
pathVal (C n) = n

pathArgName :: Pattern c p -> Path p -> c
pathArgName (PVar c) V = c
pathArgName (PCtor _ cs _) (C ix) = cs !! ix

data Branch n f a
  = forall p. Branch (Pattern n p) (Scope (Path p) f a)
  | forall p. BranchImpossible (Pattern n p)
deriving instance Functor f => Functor (Branch n f)
deriving instance Foldable f => Foldable (Branch n f)
deriving instance Traversable f => Traversable (Branch n f)

instance (Monad f, Eq1 f, Eq n) => Eq1 (Branch n f) where
  liftEq f (Branch a b) (Branch a' b') =
    case eqPattern a a' of
      Just Refl -> liftEq f b b'
      Nothing -> False
  liftEq _ (BranchImpossible a) (BranchImpossible a') =
    isJust $ eqPattern a a'
  liftEq _ _ _ = False

instance (Monad f, Eq n, Eq1 f, Eq a) => Eq (Branch n f a) where
  (==) = eq1

instance (Show n, Show1 f) => Show1 (Branch n f) where
  liftShowsPrec sp sl d (Branch a b) =
    showParen (d > 10) $
      showString "Branch "
        . showsPrec 11 a
        . showString " "
        . liftShowsPrec sp sl 11 b
  liftShowsPrec _ _ d (BranchImpossible a) =
    showParen (d > 10) $
      showString "Branch "
        . showsPrec 11 a

instance (Show n, Show1 f, Show a) => Show (Branch n f a) where
  showsPrec = showsPrec1

instance Bound (Branch n) where
  Branch a b >>>= f = Branch a (b >>>= f)
  BranchImpossible a >>>= _ = BranchImpossible a

type Ty = Term
data Term n l a
  = Var a
  | Ann (Term n l a) Usage (Term n l a)
  | Type
  | Lam n (Scope () (Term n l) a)
  | Pi Usage n (Term n l a) (Scope () (Term n l) a)
  | App (Term n l a) (Term n l a)
  | MkTensor (Term n l a) (Term n l a)
  | Tensor n Usage (Term n l a) (Scope () (Term n l) a)
  | UnpackTensor n n (Term n l a) (Scope Bool (Term n l) a)
  | MkWith (Term n l a) (Term n l a)
  | With n (Term n l a) (Scope () (Term n l) a)
  | Fst (Term n l a)
  | Snd (Term n l a)
  | Unit
  | MkUnit
  | Case (Term n l a) (NonEmpty (Branch n (Term n l) a))
  | Loc l (Term n l a)
  deriving (Functor, Foldable, Traversable)
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
  liftEq f (Tensor _ u a b) (Tensor _ u' a' b') = u == u' && liftEq f a a' && liftEq f b b'
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

instance Applicative (Term n l) where pure = return; (<*>) = ap
instance Monad (Term n l) where
  return = Var

  tm >>= f =
    case tm of
      Var a -> f a
      Ann a b c -> Ann (a >>= f) b (c >>= f)
      Type -> Type
      Lam n a -> Lam n (a >>>= f)
      Pi a n b c -> Pi a n (b >>= f) (c >>>= f)
      App a b -> App (a >>= f) (b >>= f)
      MkTensor a b -> MkTensor (a >>= f) (b >>= f)
      Tensor n u a b -> Tensor n u (a >>= f) (b >>>= f)
      UnpackTensor n1 n2 a b -> UnpackTensor n1 n2 (a >>= f) (b >>>= f)
      MkWith a b -> MkWith (a >>= f) (b >>= f)
      With n a b -> With n (a >>= f) (b >>>= f)
      Fst a -> Fst (a >>= f)
      Snd a -> Snd (a >>= f)
      Unit -> Unit
      MkUnit -> MkUnit
      Case a b -> Case (a >>= f) (fmap (>>>= f) b)
      Loc a b -> Loc a (b >>= f)

unfoldApps :: Term n l a -> (Term n l a, [Term n l a])
unfoldApps = go []
 where
  go as (App a b) = go (b : as) a
  go as a = (a, as)

lam :: Eq a => a -> Term a l a -> Term a l a
lam a = Lam a . abstract1 a

pi :: Eq a => (a, Ty a l a) -> Term a l a -> Term a l a
pi (a, ty) = Pi Many a ty . abstract1 a

lpi :: Eq a => (a, Ty a l a) -> Term a l a -> Term a l a
lpi (a, ty) = Pi One a ty . abstract1 a

forall_ :: Eq a => (a, Ty a l a) -> Term a l a -> Term a l a
forall_ (a, ty) = Pi Zero a ty . abstract1 a

arr :: IsString n => Term n l a -> Term n l a -> Term n l a
arr a b = Pi Many "_" a $ lift b

limp :: IsString n => Term n l a -> Term n l a -> Term n l a
limp a b = Pi One "_" a $ lift b

tensor :: Eq a => (a, Usage, Ty a l a) -> Ty a l a -> Ty a l a
tensor (a, u, ty) = Tensor a u ty . abstract1 a

with :: Eq a => (a, Ty a l a) -> Ty a l a -> Ty a l a
with (a, ty) = With a ty . abstract1 a

unpackTensor :: Eq a => (a, a) -> Term a l a -> Term a l a -> Term a l a
unpackTensor (x, y) m n =
  UnpackTensor x y m $
    abstract
      ( \z ->
          if z == x
            then Just False
            else if z == y then Just True else Nothing
      )
      n

varb :: (Eq a, Monad f) => a -> f a -> Branch a f a
varb a = Branch (PVar a) . abstract (\x -> if x == a then Just V else Nothing)

ctorb :: (Eq a, Monad f) => a -> [a] -> f a -> Branch a f a
ctorb a b = Branch (PCtor a b bl) . abstract (fmap C . (`elemIndex` b))
 where
  bl = length b

varb_imp :: a -> Branch a f a
varb_imp a = BranchImpossible (PVar a)

ctorb_imp :: a -> [a] -> Branch a f a
ctorb_imp a b = BranchImpossible (PCtor a b (length b))