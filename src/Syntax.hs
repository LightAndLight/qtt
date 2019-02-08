{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# language ExistentialQuantification #-}
{-# language GADTs #-}
{-# language StandaloneDeriving #-}
{-# language TemplateHaskell #-}
{-# language TypeOperators #-}
module Syntax where

import Bound.Class (Bound(..))
import Bound.Scope (Scope, abstract1, abstract)
import Control.Monad (ap)
import Control.Monad.Trans.Class (lift)
import Data.Deriving (deriveEq1, deriveShow1)
import Data.Functor.Classes (Eq1(..), Show1(..), eq1, showsPrec1)
import Data.List (elemIndex)
import Data.Semiring (Semiring(..))
import Data.Type.Equality ((:~:)(..))
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

data Pattern c p where
  PVar :: Pattern c ()
  PCtor :: c -> Int -> Pattern c Int
  PWild :: Pattern c Void
deriving instance Show c => Show (Pattern c p)

eqPattern :: Eq c => Pattern c p -> Pattern c p' -> Maybe (p :~: p')
eqPattern PVar PVar = Just Refl
eqPattern (PCtor a b) (PCtor a' b') | a == a', b == b' = Just Refl
eqPattern PWild PWild = Just Refl
eqPattern _ _ = Nothing

data Path p where
  V :: Path ()
  C :: Int -> Path Int
deriving instance Eq (Path p)
deriving instance Show (Path p)

data Branch c f a = forall p. Branch (Pattern c p) (Scope (Path p) f a)
deriving instance Functor f => Functor (Branch c f)
deriving instance Foldable f => Foldable (Branch c f)
deriving instance Traversable f => Traversable (Branch c f)

instance (Monad f, Eq1 f, Eq c) => Eq1 (Branch c f) where
  liftEq f (Branch a b) (Branch a' b') =
    case eqPattern a a' of
      Just Refl -> liftEq f b b'
      Nothing -> False

instance (Monad f, Eq c, Eq1 f, Eq a) => Eq (Branch c f a) where
  (==) = eq1

instance (Show c, Show1 f) => Show1 (Branch c f) where
  liftShowsPrec sp sl d (Branch a b) =
    showParen (d > 10) $
    showString "Branch " .
    showsPrec 11 a .
    showString " " .
    liftShowsPrec sp sl 11 b

instance (Show c, Show1 f, Show a) => Show (Branch c f a) where
  showsPrec = showsPrec1

instance Bound (Branch c) where
  Branch a b >>>= f = Branch a (b >>>= f)

type Ty = Term
data Term c a
  = Var a
  | Ann (Term c a) Usage (Term c a)
  | Type

  | Lam (Scope () (Term c) a)
  | Pi Usage (Term c a) (Scope () (Term c) a)
  | App (Term c a) (Term c a)

  | MkTensor (Term c a) (Term c a)
  | Tensor (Term c a) (Scope () (Term c) a)
  | UnpackTensor (Term c a) (Scope Bool (Term c) a)

  | MkWith (Term c a) (Term c a)
  | With (Term c a) (Scope () (Term c) a)
  | Fst (Term c a)
  | Snd (Term c a)

  | Unit
  | MkUnit

  | Case (Term c a) [Branch c (Term c) a]
deriving instance Functor (Term c)
deriving instance Foldable (Term c)
deriving instance Traversable (Term c)
deriveEq1 ''Term
deriveShow1 ''Term

instance Applicative (Term c) where; pure = return; (<*>) = ap
instance Monad (Term c) where
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

      Case a b -> Case (a >>= f) (fmap (>>>= f) b)

unfoldApps :: Term c a -> (Term c a, [Term c a])
unfoldApps = go []
  where
    go as (App a b) = go (b:as) a
    go as a = (a, as)

lam :: Eq a => a -> Term c a -> Term c a
lam a = Lam . abstract1 a

pi :: Eq a => (a, Ty c a) -> Term c a -> Term c a
pi (a, ty) = Pi Many ty . abstract1 a

lpi :: Eq a => (a, Ty c a) -> Term c a -> Term c a
lpi (a, ty) = Pi One ty . abstract1 a

forall_ :: Eq a => (a, Ty c a) -> Term c a -> Term c a
forall_ (a, ty) = Pi Zero ty . abstract1 a

arr :: Term c a -> Term c a -> Term c a
arr a b = Pi Many a $ lift b

limp :: Term c a -> Term c a -> Term c a
limp a b = Pi One a $ lift b

varb :: (Eq a, Monad f) => a -> f a -> Branch c f a
varb a = Branch PVar . abstract (\x -> if x == a then Just V else Nothing)

ctorb :: (Eq a, Monad f) => c -> [a] -> f a -> Branch c f a
ctorb a b = Branch (PCtor a bl) . abstract (fmap C . (`elemIndex` b))
  where
    bl = length b

wildb :: Monad f => f a -> Branch c f a
wildb = Branch PWild . lift

unpackTensor :: Eq a => (a, a) -> Term c a -> Term c a -> Term c a
unpackTensor (x, y) m n =
  UnpackTensor m $
  abstract
    (\z -> if z == x then Just False else if z == y then Just True else Nothing)
    n

deriving instance (Eq c, Eq a) => Eq (Term c a)
deriving instance (Show c, Show a) => Show (Term c a)