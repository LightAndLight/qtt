module Unify where

import Bound.Class (Bound(..))
import Bound.Name (Name(..))
import Bound.Scope (Scope, fromScope)
import Bound.Var (Var(..), _F, unvar)
import Control.Lens.Fold ((^?))
import Data.Map (Map)
import Data.Maybe (fromMaybe)

import qualified Bound.Name as Name
import qualified Data.Map as Map

import Context
import Syntax
import TypeError

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
  (a -> n) ->
  (a -> Maybe (Entry n l x)) ->
  Scope (Name n b) (Term n l) a ->
  Scope (Name n b) (Term n l) a ->
  Either (TypeError l n) (Subst (Term n l) a)
unifyScopes varNames ctx tm1 tm2 =
  let
    varNames' = unvar Name.name varNames
  in
    unifyTerms
      varNames'
      (unvar (const Nothing) ctx)
      (fromScope tm1)
      (fromScope tm2) >>=
    fmap Subst .
    Map.foldrWithKey
      (\k a b ->
          unvar
            -- a mapping from bound variables to terms is valid if it
            -- maps bound variables to bound variables
            (\x ->
              if Var (B x) == a
              then Right mempty
              else Left $ TypeMismatch (Var $ Name.name x) (unvar Name.name varNames <$> a))
            -- a mapping from free variables to terms is valid as long
            -- as it contains no bound variables
            (\x ->
               Map.insert x <$>
               maybe
                 (Left $
                  TypeMismatch
                    (varNames' <$> fromScope tm1)
                    (varNames' <$> fromScope tm2))
                 pure
                 (traverse (^? _F) a) <*>
               b)
            k)
      (Right mempty) .
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
  (a -> n) ->
  (a -> Maybe (Entry n l x)) ->
  Term n l a ->
  Term n l a ->
  Either (TypeError l n) (Subst (Term n l) a)
unifyTerms varNames ctx tm1 tm2 =
  case (tm1, tm2) of
    (Var a, Var b) ->
      case (ctx a, ctx b) of
        (Just CtorEntry{}, Just CtorEntry{}) ->
          if a == b
          then pure mempty
          else Left $ TypeMismatch (varNames <$> tm1) (varNames <$> tm2)
        _ -> pure $ if a == b then mempty else single a tm2
    (Var a, _) -> pure $ single a tm2
    (_, Var a) -> pure $ single a tm1
    (Lam _ b, Lam _ b') -> unifyScopes varNames ctx b b'
    (Type, Type) -> pure mempty
    (Pi a _ b c, Pi a' _ b' c') -> 
      if a /= a'
      then Left $ TypeMismatch (varNames <$> tm1) (varNames <$> tm2)
      else do
        s1 <- unifyTerms varNames ctx b b'
        s2 <- unifyScopes varNames ctx (boundSubst s1 c) (boundSubst s1 c')
        pure (s2 <> s1)
    (Ann _ _ a, _) -> unifyTerms varNames ctx a tm2
    (_, Ann _ _ a) -> unifyTerms varNames ctx tm1 a
    (App a b, App a' b') -> do
      s1 <- unifyTerms varNames ctx a a'
      s2 <- unifyTerms varNames ctx (bindSubst s1 b) (bindSubst s1 b')
      pure (s2 <> s1)
    (MkTensor a b, MkTensor a' b') -> do
      s1 <- unifyTerms varNames ctx a a'
      s2 <- unifyTerms varNames ctx (bindSubst s1 b) (bindSubst s1 b')
      pure (s2 <> s1)
    (Tensor _ a b, Tensor _ a' b') -> do
      s1 <- unifyTerms varNames ctx a a'
      s2 <- unifyScopes varNames ctx (boundSubst s1 b) (boundSubst s1 b')
      pure (s2 <> s1)
    (UnpackTensor _ _ a b, UnpackTensor _ _ a' b') -> do
      s1 <- unifyTerms varNames ctx a a'
      s2 <- unifyScopes varNames ctx (boundSubst s1 b) (boundSubst s1 b')
      pure (s2 <> s1)
    (MkWith a b, MkWith a' b') -> do
      s1 <- unifyTerms varNames ctx a a'
      s2 <- unifyTerms varNames ctx (bindSubst s1 b) (bindSubst s1 b')
      pure (s2 <> s1)
    (With _ a b, With _ a' b') -> do
      s1 <- unifyTerms varNames ctx a a'
      s2 <- unifyScopes varNames ctx (boundSubst s1 b) (boundSubst s1 b')
      pure (s2 <> s1)
    (Fst a, Fst a') -> unifyTerms varNames ctx a a'
    (Snd a, Snd a') -> unifyTerms varNames ctx a a'
    (Unit, Unit) -> pure mempty
    (MkUnit, MkUnit) -> pure mempty
    (Loc _ a, _) -> unifyTerms varNames ctx a tm2
    (_, Loc _ a) -> unifyTerms varNames ctx tm1 a
    _ ->
      if tm1 == tm2
      then pure mempty
      else Left $ TypeMismatch (varNames <$> tm1) (varNames <$> tm2)
