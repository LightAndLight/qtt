{-# language FlexibleContexts #-}
module Typecheck where

import Bound.Scope (fromScope, instantiate1, instantiate, hoistScope)
import Bound.Var (Var(..), unvar)
import Data.Bifunctor (first)
import Data.Bool (bool)
import Data.Semiring (times)

import Syntax

data TypeError a x
  = NotInScope a
  | UsingErased x
  | UsingLinear x
  | UnusedLinear (Term x)
  | UnerasedFst (Term x)
  | UnerasedSnd (Term x)
  | ExpectedType (Term x)
  | ExpectedPi (Term x)
  | ExpectedSigma (Term x)
  | ExpectedUnit (Term x)
  | TypeMismatch (Term x) (Term x)
  | Can'tInfer (Term x)
  | Deep1 (TypeError a (Var () x))
  | Deep2 (TypeError a (Var Bool x))
  deriving (Eq, Show)

eval :: Term a -> Term a
eval tm =
  case tm of
    Var a -> Var a
    Ann a _ _ -> a
    Type -> Type
    Lam a -> Lam $ hoistScope eval a
    Pi u a b -> Pi u (eval a) (hoistScope eval b)
    App a b ->
      case eval a of
        Lam s -> eval $ instantiate1 b s
        a' -> App a' $ eval b
    Pair a b -> Pair (eval a) (eval b)
    Sigma u a b -> Sigma u (eval a) (hoistScope eval b)
    Fst a ->
      case eval a of
        Pair x _ -> x
        a' -> Fst a'
    Snd a ->
      case eval a of
        Pair _ y -> y
        a' -> Snd a'
    Unit -> Unit
    MkUnit -> MkUnit
    UnpackSigma a b ->
      case eval a of
        Pair x y -> eval $ instantiate (bool x y) b
        a' -> UnpackSigma a' $ hoistScope eval b

check ::
  (Eq x, Eq a) =>
  (x -> Either a (Ty x)) ->
  (x -> Either a Usage) ->
  Term x ->
  Usage ->
  Ty x ->
  Either (TypeError a x) (x -> Either a Usage)
check ctx usages tm u_ ty_ =
  let
    u = weaken u_
    ty = eval ty_ -- pre-compute
  in
  case tm of
    Pi _ a b ->
      case ty of
        Type -> do
          _ <- check ctx ((Zero <$) . usages) a Zero Type
          _ <-
            first Deep1 $
            check
              (unvar (const $ Right $ F <$> a) (fmap (fmap F) . ctx))
              (unvar (const $ Right Zero) ((Zero <$) . usages))
              (fromScope b)
              Zero
              Type
          pure usages
        _ -> Left $ ExpectedType ty
    Lam a ->
      case ty of
        Pi u' s t -> do
          usages' <-
            first Deep1 $
            check
              (unvar (const $ Right $ F <$> s) (fmap (fmap F) . ctx))
              (unvar (const $ Right $ times u' u) usages)
              (fromScope a)
              u
              (fromScope t)
          case usages' $ B () of
            Left{} -> error "check: bound variable's usage was not found"
            Right u'' ->
              case (u', u'') of
                (One, One) -> Left $ UnusedLinear tm
                _ -> pure $ usages' . F
        _ -> Left $ ExpectedPi ty
    Sigma _ a b ->
      case ty of
        Type -> do
          _ <- check ctx ((Zero <$) . usages) a Zero Type
          _ <-
            first Deep1 $
            check
              (unvar (const $ Right $ F <$> a) (fmap (fmap F) . ctx))
              (unvar (const $ Right Zero) ((Zero <$) . usages))
              (fromScope b)
              Zero
              Type
          pure usages
        _ -> Left $ ExpectedType ty
    Pair a b ->
      case ty of
        Sigma u' s t -> do
          usages' <- check ctx usages a (times u' u) s
          check ctx usages' b u (instantiate1 (Ann a u s) t)
        _ -> Left $ ExpectedSigma ty
    Unit ->
      case ty of
        Type -> pure usages
        _ -> Left $ ExpectedType ty
    MkUnit ->
      case ty of
        Unit -> pure usages
        _ -> Left $ ExpectedUnit ty
    _ -> do
      (usages', tmTy) <- infer ctx usages tm u
      if tmTy == ty
        then pure usages'
        else Left $ TypeMismatch ty tmTy

infer ::
  (Eq a, Eq x) =>
  (x -> Either a (Ty x)) ->
  (x -> Either a Usage) ->
  Term x ->
  Usage ->
  Either (TypeError a x) (x -> Either a Usage, Ty x)
infer ctx usages tm u_ =
  let u = weaken u_ in
  fmap (fmap eval) $ -- post compute
  case tm of
    Var a -> do
      aTy <- first NotInScope $ ctx a
      u' <- first NotInScope $ usages a
      case (u, u') of
        (Zero, _) -> pure (usages, aTy)
        (One, Zero) -> Left $ UsingErased a
        (One, One) -> pure (\x -> if x == a then Right Zero else usages x, aTy)
        (One, Many) -> pure (usages, aTy)
        (Many, Zero) -> Left $ UsingErased a
        (Many, One) -> Left $ UsingLinear a
        (Many, Many) -> pure (usages, aTy)
    Ann a u' b -> do
      _ <- check ctx ((Zero <$) . usages) b Zero Type
      _ <- check ctx usages a u' b
      pure (usages, b)
    App a b -> do
      (usages', aTy) <- infer ctx usages a u
      case aTy of
        Pi u' s t -> do
          let u'' = times u' u
          usages'' <- check ctx usages' b u'' s
          pure (usages'', instantiate1 (Ann b u'' s) t)
        _ -> Left $ ExpectedPi aTy
    Fst a ->
      case u of
        Zero -> do
          (_, aTy) <- infer ctx usages a u
          case aTy of
            Sigma _ s _ -> pure (usages, s)
            _ -> Left $ ExpectedSigma aTy
        _ -> Left $ UnerasedFst tm
    Snd a ->
      case u of
        Zero -> do
          (_, aTy) <- infer ctx usages a u
          case aTy of
            Sigma _ _ t -> pure (usages, instantiate1 (Fst a) t)
            _ -> Left $ ExpectedSigma aTy
        _ -> Left $ UnerasedSnd tm
    UnpackSigma a b -> do
      (usages', aTy) <- infer ctx usages a u
      case aTy of
        Sigma u' s t -> do
          (usages'', bTy) <-
            first Deep2 $
            infer
              (unvar
                 (bool
                    (Right $ F <$> s)
                    (Right $ fromScope t >>= Var . unvar (const $ B False) F))
                 (fmap (fmap F) . ctx))
              (unvar
                 (bool (Right $ times u' u) (Right u))
                 usages')
              (fromScope b)
              u
          pure (usages'' . F, bTy >>= unvar (bool (Fst a) (Snd a)) pure)
        _ -> Left $ ExpectedSigma aTy
    _ -> Left $ Can'tInfer tm
