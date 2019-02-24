module Unify where

import Bound.Class (Bound(..))
import Bound.Scope (Scope, fromScope)
import Bound.Var (Var(..), _F, unvar)
import Control.Lens.Fold ((^?))
import Control.Monad (guard)
import Data.Map (Map)
import Data.Maybe (fromMaybe)

import qualified Data.Map as Map

import Context
import Syntax

newtype Subst f a = Subst { unSubst :: Map a (f a) }
  deriving (Eq, Show)

single :: a -> f a -> Subst f a
single a b = Subst $ Map.singleton a b

bindSubst :: (Ord a, Monad f) => Subst f a -> f a -> f a
bindSubst (Subst m) t = t >>= \x -> fromMaybe (pure x) (Map.lookup x m)

boundSubst :: (Ord a, Bound t, Monad f) => Subst f a -> t f a -> t f a
boundSubst (Subst m) t = t >>>= \x -> fromMaybe (pure x) (Map.lookup x m)

instance (Ord a, Monad f) => Semigroup (Subst f a) where
  s2 <> Subst s1 = Subst $ fmap (bindSubst s2) s1 <> unSubst s2

instance (Ord a, Monad f) => Monoid (Subst f a) where
  mempty = Subst Map.empty

unifyScopes ::
  (Ord a, Ord b) =>
  (a -> Maybe (Entry n l x)) ->
  Scope b (Term n l) a ->
  Scope b (Term n l) a ->
  Maybe (Subst (Term n l) a)
unifyScopes ctx tm1 tm2 =
  unifyTerms
    (unvar (const Nothing) ctx)
    (fromScope tm1)
    (fromScope tm2) >>=
  fmap Subst .
  Map.foldrWithKey
    (\k a b ->
        unvar
          -- a mapping from bound variables to terms is valid if it
          -- maps bound variables to bound variables
          (\x -> mempty <$ guard (Var (B x) == a))
          -- a mapping from free variables to terms is valid as long
          -- as it contains no bound variables
          (\x -> Map.insert x <$> traverse (^? _F) a <*> b)
          k)
    (Just mempty) .
    unSubst

{-

data Thing : (Nat -> Nat) -> Type where
  MkThing : (n : Nat) -> Thing (\x -> n)

MkThing x : Thing (\xx -> x)   =?   Thing (\xx -> b)


data Test : (Nat -> Nat) -> Type where
  MkTest : (n : Nat) -> Test (\x => n)

test : (a : Nat) -> Test (\x => a) -> Nat
test a b =
  case b of
    MkTest a => a


data Test2 : (Nat -> Nat -> Nat) -> Type where
  MkTest2 : (n : Nat -> Nat) -> Test2 (\x => n)

test2 : Test2 (\x => \y => x) -> Nat
test2 (MkTest2 _) impossible

-}
unifyTerms ::
  Ord a =>
  (a -> Maybe (Entry n l x)) ->
  Term n l a ->
  Term n l a ->
  Maybe (Subst (Term n l) a)
unifyTerms ctx tm1 tm2 =
  case (tm1, tm2) of
    (Var a, Var b) ->
      case (ctx a, ctx b) of
        (Just CtorEntry{}, Just CtorEntry{}) -> mempty <$ guard (a == b)
        _ -> Just $ if a == b then mempty else single a tm2
    (Var a, _) -> Just $ single a tm2
    (_, Var a) -> Just $ single a tm1
    (Lam _ b, Lam _ b') -> unifyScopes ctx b b'
    (Type, Type) -> Just mempty
    (Pi a _ b c, Pi a' _ b' c') -> do
      guard (a == a')
      s1 <- unifyTerms ctx b b'
      s2 <- unifyScopes ctx (boundSubst s1 c) (boundSubst s1 c')
      pure (s2 <> s1)
    (Ann _ _ a, _) -> unifyTerms ctx a tm2
    (_, Ann _ _ a) -> unifyTerms ctx tm1 a
    (App a b, App a' b') -> do
      s1 <- unifyTerms ctx a a'
      s2 <- unifyTerms ctx (bindSubst s1 b) (bindSubst s1 b')
      pure (s2 <> s1)
    (MkTensor a b, MkTensor a' b') -> do
      s1 <- unifyTerms ctx a a'
      s2 <- unifyTerms ctx (bindSubst s1 b) (bindSubst s1 b')
      pure (s2 <> s1)
    (Tensor _ a b, Tensor _ a' b') -> do
      s1 <- unifyTerms ctx a a'
      s2 <- unifyScopes ctx (boundSubst s1 b) (boundSubst s1 b')
      pure (s2 <> s1)
    (UnpackTensor _ _ a b, UnpackTensor _ _ a' b') -> do
      s1 <- unifyTerms ctx a a'
      s2 <- unifyScopes ctx (boundSubst s1 b) (boundSubst s1 b')
      pure (s2 <> s1)
    (MkWith a b, MkWith a' b') -> do
      s1 <- unifyTerms ctx a a'
      s2 <- unifyTerms ctx (bindSubst s1 b) (bindSubst s1 b')
      pure (s2 <> s1)
    (With _ a b, With _ a' b') -> do
      s1 <- unifyTerms ctx a a'
      s2 <- unifyScopes ctx (boundSubst s1 b) (boundSubst s1 b')
      pure (s2 <> s1)
    (Fst a, Fst a') -> unifyTerms ctx a a'
    (Snd a, Snd a') -> unifyTerms ctx a a'
    (Unit, Unit) -> pure mempty
    (MkUnit, MkUnit) -> pure mempty
    (Loc _ a, _) -> unifyTerms ctx a tm2
    (_, Loc _ a) -> unifyTerms ctx tm1 a
    _ -> if tm1 == tm2 then pure mempty else Nothing
