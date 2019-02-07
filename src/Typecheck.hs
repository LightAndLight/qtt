{-# language DeriveFunctor #-}
{-# language FlexibleContexts #-}
module Typecheck where

import Bound.Scope (fromScope, instantiate1, instantiate, hoistScope)
import Bound.Var (Var(..), unvar)
import Control.Lens.Setter (over, mapped)
import Control.Lens.Tuple (_3)
import Data.Bifunctor (first)
import Data.Bool (bool)
import Data.Semiring (times)

import Syntax

data Entry a
  = InductiveEntry { _entryType :: Ty a, _entryCtors :: [(a, Term a)] }
  | BindingEntry { _entryType :: Ty a }
  deriving (Eq, Show, Functor)

data TypeError a x
  = NotInScope a
  | UsingErased x
  | UnusedLinear x
  | UnerasedFst (Term x)
  | UnerasedSnd (Term x)
  | ExpectedType (Term x)
  | ExpectedPi (Term x)
  | ExpectedTensor (Term x)
  | ExpectedWith (Term x)
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
    MkWith a b -> MkWith (eval a) (eval b)
    With a b -> With (eval a) (hoistScope eval b)
    Fst a ->
      case eval a of
        MkWith x _ -> x
        a' -> Fst a'
    Snd a ->
      case eval a of
        MkWith _ y -> y
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

mergeUsages ::
  (x -> Either a Usage) ->
  (x -> Either a Usage) ->
  (x -> Either a Usage)
mergeUsages a b x = do
  uA <- a x
  uB <- b x
  case (uA, uB) of
    (Zero, Zero) -> pure Zero
    (Zero, One) -> pure Zero
    (Zero, Many) -> error "mergeUsages: zero as many"
    (One, Zero) -> pure Zero
    (One, One) -> pure One
    (One, Many) -> error "mergeUsages: one as many"
    (Many, Zero) -> error "mergeUsages: many as zero"
    (Many, One) -> error "mergeUsages: many as one"
    (Many, Many) -> pure Many

checkZero ::
  (Eq x, Eq a) =>
  (x -> Either a (Entry x)) ->
  (x -> Either a Usage) ->
  Term x ->
  Ty x ->
  Either (TypeError a x) (x -> Either a Usage)
checkZero ctx usages tm = check ctx ((Zero <$) . usages) tm Zero . eval

check ::
  (Eq x, Eq a) =>
  (x -> Either a (Entry x)) ->
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
          _ <- checkZero ctx usages a Type
          _ <-
            first Deep1 $
            check
              (unvar (const $ Right $ BindingEntry (F <$> a)) (fmap (fmap F) . ctx))
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
              (unvar (const $ Right $ BindingEntry (F <$> s)) (fmap (fmap F) . ctx))
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
          _ <- checkZero ctx usages a Type
          _ <-
            first Deep1 $
            check
              (unvar (const $ Right $ BindingEntry (F <$> a)) (fmap (fmap F) . ctx))
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
    UnpackTensor a b -> do
      (usages', aUsage, aTy) <- infer ctx usages a u
      case aTy of
        Tensor s t -> do
          usages'' <-
            first Deep2 $
            check
              (unvar
                 (Right . BindingEntry .
                  bool
                    (F <$> s)
                    (fromScope t >>= Var . unvar (const $ B False) F))
                 (fmap (fmap F) . ctx))
              (unvar
                 (bool (Right aUsage) (Right aUsage))
                 usages')
              (fromScope b)
              u
              (F <$> ty)
          first Deep2 $ unsafeCheckConsumed aUsage (B False) usages''
          first Deep2 $ unsafeCheckConsumed aUsage (B True) usages''
          pure $ usages'' . F
        _ -> Left $ ExpectedTensor aTy
    With a b ->
      case ty of
        Type -> do
          _ <- checkZero ctx usages a Type
          _ <-
            first Deep1 $
            check
              (unvar (const $ Right $ BindingEntry $ F <$> a) (fmap (fmap F) . ctx))
              (unvar (const $ Right Zero) ((Zero <$) . usages))
              (fromScope b)
              Zero
              Type
          pure usages
        _ -> Left $ ExpectedType ty
    MkWith a b ->
      case ty of
        With s t -> do
          usagesA <- check ctx usages a u s
          usagesB <- check ctx usages b u (instantiate1 (Ann a u s) t)
          pure $ mergeUsages usagesA usagesB
        _ -> Left $ ExpectedWith ty
    Unit ->
      case ty of
        Type -> pure usages
        _ -> Left $ ExpectedType ty
    MkUnit ->
      case ty of
        Unit -> pure usages
        _ -> Left $ ExpectedUnit ty
    _ -> do
      (usages', _, tmTy) <- infer ctx usages tm u
      if tmTy == ty
        then pure usages'
        else Left $ TypeMismatch ty tmTy

infer ::
  (Eq a, Eq x) =>
  (x -> Either a (Entry x)) ->
  (x -> Either a Usage) ->
  Term x ->
  Usage ->
  Either (TypeError a x) (x -> Either a Usage, Usage, Ty x)
infer ctx usages tm u =
  over (mapped._3) eval $ -- post compute
  case tm of
    Var a -> do
      aTy <- fmap _entryType . first NotInScope $ ctx a
      u' <- first NotInScope $ usages a
      case (u, u') of
        (Zero, _) -> pure (usages, u', aTy)
        (One, Zero) -> Left $ UsingErased a
        (One, One) -> pure (\x -> if x == a then Right Zero else usages x, u', aTy)
        (One, Many) -> pure (usages, u', aTy)
        (Many, Zero) -> Left $ UsingErased a
        (Many, One) -> pure (\x -> if x == a then Right Zero else usages x, u', aTy)
        (Many, Many) -> pure (usages, u', aTy)
    Ann a u' b -> do
      _ <- check ctx ((Zero <$) . usages) b Zero Type
      usages' <- check ctx usages a u' b
      pure (usages', u', b)
    App a b -> do
      (usages', aUsage, aTy) <- infer ctx usages a u
      case aTy of
        Pi u' s t -> do
          let u'' = times u' aUsage
          usages'' <- check ctx usages' b u'' s
          pure (usages'', aUsage, instantiate1 (Ann b u'' s) t)
        _ -> Left $ ExpectedPi aTy
    Fst a -> do
      (usages', aUsage, aTy) <- infer ctx usages a u
      case aTy of
        With s _ -> pure (usages', aUsage, s)
        _ -> Left $ ExpectedWith aTy
    Snd a -> do
      (usages', aUsage, aTy) <- infer ctx usages a u
      case aTy of
        With _ t -> pure (usages', aUsage, (instantiate1 (Fst a) t))
        _ -> Left $ ExpectedWith aTy
    _ -> Left $ Can'tInfer tm
