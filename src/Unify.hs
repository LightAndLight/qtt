{-# LANGUAGE LambdaCase #-}

module Unify where

import Bound.Class (Bound (..))
import Bound.Scope (Scope, fromScope)
import Bound.Var (Var (..), unvar, _F)
import Control.Lens.Fold ((^?))
import Data.Bool (bool)
import Data.Map (Map)
import Data.Maybe (fromMaybe)

import qualified Data.Map as Map

import Context
import Syntax
import TypeError

newtype Subst f a = Subst {unSubst :: Map a (f a)}
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
  (a -> n) ->
  (a -> Maybe (Entry n l x)) ->
  (b -> n, Scope b (Term n l) a) ->
  (b -> n, Scope b (Term n l) a) ->
  Either (TypeError l n) (Subst (Term n l) a)
unifyScopes varNames1 varNames2 ctx (n1, tm1) (n2, tm2) =
  let varNames1' = unvar n1 varNames1
      varNames2' = unvar n2 varNames2
   in unifyTerms
        varNames1'
        varNames2'
        (unvar (const Nothing) ctx)
        (fromScope tm1)
        (fromScope tm2)
        >>= fmap Subst
          . Map.foldrWithKey
            ( \k a b ->
                unvar
                  -- a mapping from bound variables to terms is valid if it
                  -- maps bound variables to bound variables
                  ( \x ->
                      if Var (B x) == a
                        then Right mempty
                        else Left $ TypeMismatch (Var $ n1 x) (varNames2' <$> a)
                  )
                  -- a mapping from free variables to terms is valid as long
                  -- as it contains no bound variables
                  ( \x ->
                      Map.insert x
                        <$> maybe
                          ( Left $
                              TypeMismatch
                                (varNames1' <$> fromScope tm1)
                                (varNames2' <$> fromScope tm2)
                          )
                          pure
                          (traverse (^? _F) a)
                        <*> b
                  )
                  k
            )
            (Right mempty)
          . unSubst

unifyApps ::
  Ord a =>
  (a -> n) ->
  (a -> n) ->
  (a -> Maybe (Entry n l x)) ->
  Term n l a ->
  Term n l a ->
  Either (TypeError l n) (Subst (Term n l) a)
unifyApps varNames1 varNames2 ctx tm1 tm2 =
  let (f, xs) = unfoldApps tm1

      fvar =
        maybe True (\case CtorEntry{} -> False; _ -> True) $
          case f of
            Var a -> ctx a
            _ -> Nothing

      unifyMany s [] [] = Right s
      unifyMany s (a : as) (b : bs) = do
        s1 <- unifyTerms varNames1 varNames2 ctx (bindSubst s a) (bindSubst s b)
        unifyMany (s1 <> s) as bs
      unifyMany _ _ _ =
        Left $ TypeMismatch (varNames1 <$> tm1) (varNames2 <$> tm2)
   in case (fvar, xs) of
        (True, _ : _) ->
          Left $ UnknownSolution (varNames1 <$> tm1) (varNames2 <$> tm2)
        _ -> do
          let (f', xs') = unfoldApps tm2
          s1 <- unifyTerms varNames1 varNames2 ctx f f'
          unifyMany s1 xs xs'

unifyTerms ::
  Ord a =>
  (a -> n) ->
  (a -> n) ->
  (a -> Maybe (Entry n l x)) ->
  Term n l a ->
  Term n l a ->
  Either (TypeError l n) (Subst (Term n l) a)
unifyTerms varNames1 varNames2 ctx tm1 tm2 =
  case (tm1, tm2) of
    (Var a, Var b) ->
      case (ctx a, ctx b) of
        (Just CtorEntry{}, Just CtorEntry{}) ->
          if a == b
            then pure mempty
            else Left $ TypeMismatch (varNames1 <$> tm1) (varNames2 <$> tm2)
        _ -> pure $ if a == b then mempty else single a tm2
    (Var a, _) -> pure $ single a tm2
    (_, Var a) -> pure $ single a tm1
    (Lam n b, Lam n' b') -> unifyScopes varNames1 varNames2 ctx (const n, b) (const n', b')
    (Type, Type) -> pure mempty
    (Pi a n b c, Pi a' n' b' c') ->
      if a /= a'
        then Left $ TypeMismatch (varNames1 <$> tm1) (varNames2 <$> tm2)
        else do
          s1 <- unifyTerms varNames1 varNames2 ctx b b'
          s2 <- unifyScopes varNames1 varNames2 ctx (const n, boundSubst s1 c) (const n', boundSubst s1 c')
          pure (s2 <> s1)
    (Ann _ _ a, _) -> unifyTerms varNames1 varNames2 ctx a tm2
    (_, Ann _ _ a) -> unifyTerms varNames1 varNames2 ctx tm1 a
    (App{}, _) -> unifyApps varNames1 varNames2 ctx tm1 tm2
    (_, App{}) -> unifyApps varNames1 varNames2 ctx tm2 tm1
    (MkTensor a b, MkTensor a' b') -> do
      s1 <- unifyTerms varNames1 varNames2 ctx a a'
      s2 <- unifyTerms varNames1 varNames2 ctx (bindSubst s1 b) (bindSubst s1 b')
      pure (s2 <> s1)
    (Tensor n u a b, Tensor n' u' a' b') -> do
      if u /= u'
        then Left $ TypeMismatch (varNames1 <$> tm1) (varNames2 <$> tm2)
        else do
          s1 <- unifyTerms varNames1 varNames2 ctx a a'
          s2 <- unifyScopes varNames1 varNames2 ctx (const n, boundSubst s1 b) (const n', boundSubst s1 b')
          pure (s2 <> s1)
    (UnpackTensor n1 n2 a b, UnpackTensor n1' n2' a' b') -> do
      s1 <- unifyTerms varNames1 varNames2 ctx a a'
      s2 <- unifyScopes varNames1 varNames2 ctx (bool n1 n2, boundSubst s1 b) (bool n1' n2', boundSubst s1 b')
      pure (s2 <> s1)
    (MkWith a b, MkWith a' b') -> do
      s1 <- unifyTerms varNames1 varNames2 ctx a a'
      s2 <- unifyTerms varNames1 varNames2 ctx (bindSubst s1 b) (bindSubst s1 b')
      pure (s2 <> s1)
    (With n a b, With n' a' b') -> do
      s1 <- unifyTerms varNames1 varNames2 ctx a a'
      s2 <- unifyScopes varNames1 varNames2 ctx (const n, boundSubst s1 b) (const n', boundSubst s1 b')
      pure (s2 <> s1)
    (Fst a, Fst a') -> unifyTerms varNames1 varNames2 ctx a a'
    (Snd a, Snd a') -> unifyTerms varNames1 varNames2 ctx a a'
    (Unit, Unit) -> pure mempty
    (MkUnit, MkUnit) -> pure mempty
    (Loc _ a, _) -> unifyTerms varNames1 varNames2 ctx a tm2
    (_, Loc _ a) -> unifyTerms varNames1 varNames2 ctx tm1 a
    _ ->
      if tm1 == tm2
        then pure mempty
        else Left $ TypeMismatch (varNames1 <$> tm1) (varNames2 <$> tm2)

unifyInductive ::
  Ord a =>
  (a -> n) ->
  (a -> n) ->
  (a -> Maybe (Entry n l x)) ->
  Term n l a ->
  Term n l a ->
  Either (TypeError l n) (Subst (Term n l) a)
unifyInductive varNames1 varNames2 ctx tm1 tm2 =
  let (f, xs) = unfoldApps tm1
      (f', xs') = unfoldApps tm2

      unifyMany s [] [] = Right s
      unifyMany s (a : as) (b : bs) = do
        s1 <- unifyTerms varNames1 varNames2 ctx (bindSubst s a) (bindSubst s b)
        unifyMany (s1 <> s) as bs
      unifyMany _ _ _ =
        Left $ TypeMismatch (varNames1 <$> tm1) (varNames2 <$> tm2)
   in case (f, f') of
        (Var a, Var a')
          | Just InductiveEntry{} <- ctx a
            , Just InductiveEntry{} <- ctx a' ->
            if a /= a'
              then Left $ TypeMismatch (varNames1 <$> tm1) (varNames2 <$> tm2)
              else unifyMany mempty xs xs'
        _ -> unifyTerms varNames1 varNames2 ctx tm1 tm2