{-# language DeriveFunctor #-}
{-# language EmptyCase #-}
{-# language FlexibleContexts #-}
{-# language GADTs #-}
{-# language LambdaCase #-}
module Typecheck where

import Bound.Scope (Scope, fromScope, toScope, instantiate1, instantiate)
import Bound.Var (Var(..), unvar)
import Control.Lens.Setter (over, mapped)
import Control.Lens.Tuple (_3)
import Data.Bifunctor (first)
import Data.Bool (bool)
import Data.Semiring (times)

import Syntax

data Entry c a
  = InductiveEntry { _entryType :: Ty c a, _entryCtors :: [(a, Term c a)] }
  | BindingEntry { _entryType :: Ty c a }
  deriving (Eq, Show, Functor)

data TypeError c a x
  = NotInScope a
  | UsingErased x
  | UnusedLinear x
  | UnerasedFst (Term c x)
  | UnerasedSnd (Term c x)
  | ExpectedType (Term c x)
  | ExpectedPi (Term c x)
  | ExpectedTensor (Term c x)
  | ExpectedWith (Term c x)
  | ExpectedUnit (Term c x)
  | TypeMismatch (Term c x) (Term c x)
  | Can'tInfer (Term c x)
  | Deep1 (TypeError c a (Var () x))
  | Deep2 (TypeError c a (Var Bool x))
  deriving (Eq, Show)

pickBranch :: (a -> c -> Bool) -> Term c a -> [Term c a] -> [Branch c (Term c) a] -> Term c a
pickBranch _ _ _ [] = error "pickBranch: no branch to follow"
pickBranch eq f xs (Branch p v : bs) =
  case p of
    PVar -> instantiate (\case; V -> foldl App f xs) v
    PCtor n count ->
      case f of
        Var n' ->
          if n' `eq` n
          then
            if count == length xs
            then instantiate (\case; C x -> xs !! x) v
            else error "pickBack: incorrect number of arguments to constructor"
          else pickBranch eq f xs bs
        _ -> error "pickBranch: can't match on non-var"
    PWild -> instantiate (\case {}) v

eval :: (a -> c -> Bool) -> Term c a -> Term c a
eval cmp tm =
  case tm of
    Var a -> Var a
    Ann a _ _ -> a
    Type -> Type
    Lam a -> Lam $ evalScope cmp a
    Pi u a b -> Pi u (eval cmp a) (evalScope cmp b)
    App a b ->
      case eval cmp a of
        Lam s -> eval cmp $ instantiate1 b s
        a' -> App a' $ eval cmp b
    MkTensor a b -> MkTensor (eval cmp a) (eval cmp b)
    Tensor a b -> Tensor (eval cmp a) (evalScope cmp b)
    MkWith a b -> MkWith (eval cmp a) (eval cmp b)
    With a b -> With (eval cmp a) (evalScope cmp b)
    Fst a ->
      case eval cmp a of
        MkWith x _ -> x
        a' -> Fst a'
    Snd a ->
      case eval cmp a of
        MkWith _ y -> y
        a' -> Snd a'
    Unit -> Unit
    MkUnit -> MkUnit
    UnpackTensor a b ->
      case eval cmp a of
        MkTensor x y -> eval cmp $ instantiate (bool x y) b
        a' -> UnpackTensor a' $ evalScope cmp b
    Case a bs -> let (f, xs) = unfoldApps (eval cmp a) in pickBranch cmp f xs bs
  where
    evalScope :: (a -> c -> Bool) -> Scope b (Term c) a -> Scope b (Term c) a
    evalScope cmp' = toScope . eval (unvar (\_ _ -> False) cmp') . fromScope

unsafeGetUsage :: a -> (a -> Either b c) -> c
unsafeGetUsage a usages =
  case usages a of
    Left{} -> error "check: bound variable's usage was not found"
    Right u -> u

unsafeCheckConsumed ::
  Usage -> -- ^ Expected usage
  x -> -- ^ Variable
  (x -> Either b Usage) -> -- ^ Usages
  Either (TypeError c a x) ()
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
  (Eq x, Eq c, Eq a) =>
  (x -> c -> Bool) ->
  (x -> Either a (Entry c x)) ->
  (x -> Either a Usage) ->
  Term c x ->
  Ty c x ->
  Either (TypeError c a x) (x -> Either a Usage)
checkZero cmp ctx usages tm = check cmp ctx ((Zero <$) . usages) tm Zero . eval cmp

check ::
  (Eq x, Eq c, Eq a) =>
  (x -> c -> Bool) ->
  (x -> Either a (Entry c x)) ->
  (x -> Either a Usage) ->
  Term c x ->
  Usage ->
  Ty c x ->
  Either (TypeError c a x) (x -> Either a Usage)
check cmp ctx usages tm u ty_ =
  let ty = eval cmp ty_ in -- pre-compute
  case tm of
    Pi _ a b ->
      case ty of
        Type -> do
          _ <- checkZero cmp ctx usages a Type
          _ <-
            first Deep1 $
            check
              (unvar (\_ _ -> False) cmp)
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
              (unvar (\_ _ -> False) cmp)
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
          _ <- checkZero cmp ctx usages a Type
          _ <-
            first Deep1 $
            check
              (unvar (\_ _ -> False) cmp)
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
          usages' <- check cmp ctx usages a u s
          check cmp ctx usages' b u (instantiate1 (Ann a u s) t)
        _ -> Left $ ExpectedTensor ty
    UnpackTensor a b -> do
      (usages', aUsage, aTy) <- infer cmp ctx usages a u
      case aTy of
        Tensor s t -> do
          usages'' <-
            first Deep2 $
            check
              (unvar (\_ _ -> False) cmp)
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
          _ <- checkZero cmp ctx usages a Type
          _ <-
            first Deep1 $
            check
              (unvar (\_ _ -> False) cmp)
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
          usagesA <- check cmp ctx usages a u s
          usagesB <- check cmp ctx usages b u (instantiate1 (Ann a u s) t)
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
    Case _ _ -> undefined
    _ -> do
      (usages', _, tmTy) <- infer cmp ctx usages tm u
      if tmTy == ty
        then pure usages'
        else Left $ TypeMismatch ty tmTy

infer ::
  (Eq c, Eq a, Eq x) =>
  (x -> c -> Bool) ->
  (x -> Either a (Entry c x)) ->
  (x -> Either a Usage) ->
  Term c x ->
  Usage ->
  Either (TypeError c a x) (x -> Either a Usage, Usage, Ty c x)
infer cmp ctx usages tm u =
  over (mapped._3) (eval cmp) $ -- post compute
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
      _ <- check cmp ctx ((Zero <$) . usages) b Zero Type
      usages' <- check cmp ctx usages a u' b
      pure (usages', u', b)
    App a b -> do
      (usages', aUsage, aTy) <- infer cmp ctx usages a u
      case aTy of
        Pi u' s t -> do
          let u'' = times u' aUsage
          usages'' <- check cmp ctx usages' b u'' s
          pure (usages'', aUsage, instantiate1 (Ann b u'' s) t)
        _ -> Left $ ExpectedPi aTy
    Fst a -> do
      (usages', aUsage, aTy) <- infer cmp ctx usages a u
      case aTy of
        With s _ -> pure (usages', aUsage, s)
        _ -> Left $ ExpectedWith aTy
    Snd a -> do
      (usages', aUsage, aTy) <- infer cmp ctx usages a u
      case aTy of
        With _ t -> pure (usages', aUsage, (instantiate1 (Fst a) t))
        _ -> Left $ ExpectedWith aTy
    _ -> Left $ Can'tInfer tm
