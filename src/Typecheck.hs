{-# language FlexibleContexts #-}
module Typecheck where

import Bound.Scope (fromScope, instantiate1, instantiate, hoistScope)
import Bound.Var (Var(..), unvar)
import Control.Lens.Setter (over, mapped)
import Data.Bifunctor (first)
import Data.Bool (bool)
import Data.Semiring (times)

import Context
import Syntax

data TypeError a x
  = NotInScope a
  | UsingErased x
  | UsingLinear x
  | UnusedLinear x
  | UnerasedFst (Term x)
  | UnerasedSnd (Term x)
  | ExpectedType (Term x)
  | ExpectedPi (Term x)
  | ExpectedTensor (Term x)
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
    MkTensor a b -> MkTensor (eval a) (eval b)
    Tensor a b -> Tensor (eval a) (hoistScope eval b)
    Fst a ->
      case eval a of
        MkTensor x _ -> x
        a' -> Fst a'
    Snd a ->
      case eval a of
        MkTensor _ y -> y
        a' -> Snd a'
    Unit -> Unit
    MkUnit -> MkUnit
    UnpackTensor a b ->
      case eval a of
        MkTensor x y -> eval $ instantiate (bool x y) b
        a' -> UnpackTensor a' $ hoistScope eval b

unsafeGetUsage :: a -> (a -> Either b c) -> c
unsafeGetUsage a usages =
  case usages a of
    Left{} -> error "check: bound variable's usage was not found"
    Right u -> u

unsafeCheckConsumed ::
  Usage -> -- ^ Expected usage
  x -> -- ^ Variable
  (x -> Either b Usage) -> -- ^ Usages
  Either (TypeError a x) ()
unsafeCheckConsumed u a usages =
  let
    u' = unsafeGetUsage a usages
  in
    case (u, u') of
      (One, One) -> Left $ UnusedLinear a
      _ -> pure ()

check ::
  (Eq x, Eq a) =>
  (x -> Either a (Ty x)) ->
  (x -> Either a Usage) ->
  Term x ->
  Usage ->
  Ty x ->
  Either (TypeError a x) (x -> Either a Usage)
check ctx usages tm u ty_ =
  let ty = eval ty_ in -- pre-compute
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
          first Deep1 $ unsafeCheckConsumed u' (B ()) usages'
          pure $ usages' . F
        _ -> Left $ ExpectedPi ty
    Tensor a b ->
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
    MkTensor a b ->
      case ty of
        Tensor s t -> do
          usages' <- check ctx usages a u s
          check ctx usages' b u (instantiate1 (Ann a u s) t)
        _ -> Left $ ExpectedTensor ty
    Unit ->
      case ty of
        Type -> pure usages
        _ -> Left $ ExpectedType ty
    MkUnit ->
      case ty of
        Unit -> pure usages
        _ -> Left $ ExpectedUnit ty
    _ -> do
      (usages', Entry _ tmTy) <- infer ctx usages tm u
      if tmTy == ty
        then pure usages'
        else Left $ TypeMismatch ty tmTy

infer ::
  (Eq a, Eq x) =>
  (x -> Either a (Ty x)) ->
  (x -> Either a Usage) ->
  Term x ->
  Usage ->
  Either (TypeError a x) (x -> Either a Usage, Entry x)
infer ctx usages tm u =
  over (mapped.mapped.entryType) eval $ -- post compute
  case tm of
    Var a -> do
      aTy <- first NotInScope $ ctx a
      u' <- first NotInScope $ usages a
      case (u, u') of
        (Zero, _) -> pure (usages, Entry u' aTy)
        (One, Zero) -> Left $ UsingErased a
        (One, One) -> pure (\x -> if x == a then Right Zero else usages x, Entry u' aTy)
        (One, Many) -> pure (usages, Entry u' aTy)
        (Many, Zero) -> Left $ UsingErased a
        (Many, One) -> pure (\x -> if x == a then Right Zero else usages x, Entry u' aTy)
        (Many, Many) -> pure (usages, Entry u' aTy)
    Ann a u' b -> do
      _ <- check ctx ((Zero <$) . usages) b Zero Type
      _ <- check ctx usages a u' b
      pure (usages, Entry u' b)
    App a b -> do
      (usages', Entry aUsage aTy) <- infer ctx usages a u
      case aTy of
        Pi u' s t -> do
          let u'' = times u' aUsage
          usages'' <- check ctx usages' b u'' s
          pure (usages'', Entry aUsage $ instantiate1 (Ann b u'' s) t)
        _ -> Left $ ExpectedPi aTy
    Fst a ->
      case u of
        Zero -> do
          (_, Entry aUsage aTy) <- infer ctx usages a u
          case aTy of
            Tensor s _ -> pure (usages, Entry aUsage s)
            _ -> Left $ ExpectedTensor aTy
        _ -> Left $ UnerasedFst tm
    Snd a ->
      case u of
        Zero -> do
          (_, Entry aUsage aTy) <- infer ctx usages a u
          case aTy of
            Tensor _ t -> pure (usages, Entry aUsage $ instantiate1 (Fst a) t)
            _ -> Left $ ExpectedTensor aTy
        _ -> Left $ UnerasedSnd tm
    UnpackTensor a b -> do
      (usages', Entry aUsage aTy) <- infer ctx usages a u
      case aTy of
        Tensor s t -> do
          (usages'', Entry bUsage bTy) <-
            first Deep2 $
            infer
              (unvar
                 (bool
                    (Right $ F <$> s)
                    (Right $ fromScope t >>= Var . unvar (const $ B False) F))
                 (fmap (fmap F) . ctx))
              (unvar
                 (bool (Right aUsage) (Right aUsage))
                 usages')
              (fromScope b)
              u
          first Deep2 $ unsafeCheckConsumed aUsage (B False) usages''
          first Deep2 $ unsafeCheckConsumed aUsage (B True) usages''
          pure
            ( usages'' . F
            , Entry bUsage $ bTy >>= unvar (bool (Fst a) (Snd a)) pure
            )
        _ -> Left $ ExpectedTensor aTy
    _ -> Left $ Can'tInfer tm
