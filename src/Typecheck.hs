{-# language DeriveFunctor #-}
{-# language FlexibleContexts #-}
{-# language TemplateHaskell #-}
module Typecheck where

import Bound.Name (Name(..), instantiateName, instantiate1Name)
import Bound.Scope (fromScope, instantiate1, hoistScope)
import Bound.Var (Var(..), unvar)
import Control.Applicative ((<|>))
import Control.Comonad (extract)
import Control.Lens.Setter (over, mapped)
import Control.Lens.TH (makeLenses)
import Control.Monad (guard)
import Data.Bool (bool)
import Data.Semiring (times)

import qualified Bound.Name as Bound

import Syntax

data Entry n l a
  = Entry
  { _entryUsage :: Usage
  , _entryType :: Term n l a
  } deriving (Eq, Show, Functor)
makeLenses ''Entry

data TypeError l a
  = NotInScope a
  | UsingErased a
  | UnusedLinear a
  | ExpectedType (Term a l a)
  | ExpectedPi (Term a l a)
  | ExpectedTensor (Term a l a)
  | ExpectedWith (Term a l a)
  | ExpectedUnit (Term a l a)
  | TypeMismatch (Term a l a) (Term a l a)
  | Can'tInfer (Term a l a)
  deriving (Eq, Show)

eval :: Term n l a -> Term n l a
eval tm =
  case tm of
    Loc _ a -> eval a
    Var a -> Var a
    Ann a _ _ -> a
    Type -> Type
    Lam n a -> Lam n $ hoistScope eval a
    Pi u n a b -> Pi u n (eval a) (hoistScope eval b)
    App a b ->
      case eval a of
        Lam _ s -> eval $ instantiate1 b s
        a' -> App a' $ eval b
    MkTensor a b -> MkTensor (eval a) (eval b)
    Tensor n a b -> Tensor n (eval a) (hoistScope eval b)
    MkWith a b -> MkWith (eval a) (eval b)
    With n a b -> With n (eval a) (hoistScope eval b)
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
    UnpackTensor m n a b ->
      case eval a of
        MkTensor x y -> eval $ instantiateName (bool x y) b
        a' -> UnpackTensor m n a' $ hoistScope eval b

unsafeGetUsage :: a -> (a -> Maybe b) -> b
unsafeGetUsage a usages =
  case usages a of
    Nothing -> error "check: bound variable's usage was not found"
    Just u -> u

unsafeCheckConsumed ::
  (x -> a) -> -- ^ Variable names
  Usage -> -- ^ Expected usage
  x -> -- ^ Variable
  (x -> Maybe Usage) -> -- ^ Usages
  Either (TypeError l a) ()
unsafeCheckConsumed names u a usages =
  let
    u' = unsafeGetUsage a usages
  in
    case (u, u') of
      (One, One) -> Left $ UnusedLinear $ names a
      _ -> pure ()

mergeUsages ::
  (x -> Maybe Usage) ->
  (x -> Maybe Usage) ->
  (x -> Maybe Usage)
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
  (a -> x) ->
  (x -> a) ->
  (x -> Maybe (Ty a l x)) ->
  (x -> Maybe Usage) ->
  Term a l x ->
  Ty a l x ->
  Either (TypeError l a) (x -> Maybe Usage)
checkZero depth names ctx usages tm =
  check depth names ctx ((Zero <$) . usages) tm Zero . eval

check ::
  (Eq x, Eq a) =>
  (a -> x) ->
  (x -> a) ->
  (x -> Maybe (Ty a l x)) ->
  (x -> Maybe Usage) ->
  Term a l x ->
  Usage ->
  Ty a l x ->
  Either (TypeError l a) (x -> Maybe Usage)
check depth names ctx usages tm u ty_ =
  let ty = eval ty_ in -- pre-compute
  case tm of
    Type ->
      case ty of
        Type -> pure usages
        _ -> Left $ ExpectedType $ names <$> ty
    Pi _ _ a b ->
      case ty of
        Type -> do
          _ <- checkZero depth names ctx usages a Type
          _ <-
            checkZero
              (F . depth)
              (unvar Bound.name names)
              (fmap (fmap F) . unvar (const (Just a) . extract) ctx)
              (unvar (const (Just Zero) . extract) usages)
              (fromScope b)
              Type
          pure usages
        _ -> Left $ ExpectedType $ names <$> ty
    Lam n a ->
      case ty of
        Pi u' _ s t -> do
          usages' <-
            check
              (F . depth)
              (unvar Bound.name names)
              (fmap (fmap F) . unvar (const (Just s) . extract) ctx)
              (unvar (const (Just $ times u' u) . extract) usages)
              (fromScope a)
              u
              (fromScope t)
          unsafeCheckConsumed
            (unvar Bound.name names)
            (times u' u)
            (B $ Name n ())
            usages'
          pure $ usages' . F
        _ -> Left $ ExpectedPi $ names <$> ty
    Tensor _ a b ->
      case ty of
        Type -> do
          _ <- checkZero depth names ctx usages a Type
          _ <-
            checkZero
              (F . depth)
              (unvar Bound.name names)
              (fmap (fmap F) . unvar (const (Just a) . extract) ctx)
              (unvar (const (Just Zero) . extract) usages)
              (fromScope b)
              Type
          pure usages
        _ -> Left $ ExpectedType $ names <$> ty
    MkTensor a b ->
      case ty of
        Tensor _ s t -> do
          usages' <- check depth names ctx usages a u s
          check depth names ctx usages' b u (instantiate1 (Ann a u s) t)
        _ -> Left $ ExpectedTensor $ names <$> ty
    UnpackTensor n1 n2 a b -> do
      (usages', Entry aUsage aTy) <- infer depth names ctx usages a u
      case aTy of
        Tensor _ s t -> do
          let names' = unvar Bound.name names
          usages'' <-
            check
              (F . depth)
              names'
              (fmap (fmap F) . unvar (Just . bool s (instantiate1Name (Fst a) t) . extract) ctx)
              (unvar (const (Just aUsage) . extract) usages')
              (fromScope b)
              u
              (F <$> ty)
          unsafeCheckConsumed names' aUsage (B $ Name n1 False) usages''
          unsafeCheckConsumed names' aUsage (B $ Name n2 True) usages''
          pure $ usages'' . F
        _ -> Left $ ExpectedTensor $ names <$> aTy
    With _ a b ->
      case ty of
        Type -> do
          _ <- checkZero depth names ctx usages a Type
          _ <-
            checkZero
              (F . depth)
              (unvar Bound.name names)
              (fmap (fmap F) . unvar (const (Just a)) ctx)
              (unvar (const (Just Zero)) usages)
              (fromScope b)
              Type
          pure usages
        _ -> Left $ ExpectedType $ names <$> ty
    MkWith a b ->
      case ty of
        With _ s t -> do
          usagesA <- check depth names ctx usages a u s
          usagesB <- check depth names ctx usages b u (instantiate1 (Ann a u s) t)
          pure $ mergeUsages usagesA usagesB
        _ -> Left $ ExpectedWith $ names <$> ty
    Unit ->
      case ty of
        Type -> pure usages
        _ -> Left $ ExpectedType $ names <$> ty
    MkUnit ->
      case ty of
        Unit -> pure usages
        _ -> Left $ ExpectedUnit $ names <$> ty
    _ -> do
      (usages', Entry _ tmTy) <- infer depth names ctx usages tm u
      if tmTy == ty
        then pure usages'
        else Left $ TypeMismatch (names <$> ty) (names <$> tmTy)

infer ::
  (Eq a, Eq x) =>
  (a -> x) ->
  (x -> a) ->
  (x -> Maybe (Ty a l x)) ->
  (x -> Maybe Usage) ->
  Term a l x ->
  Usage ->
  Either (TypeError l a) (x -> Maybe Usage, Entry a l x)
infer depth names ctx usages tm u =
  over (mapped.mapped.entryType) eval $ -- post compute
  case tm of
    Var a -> do
      aTy <- maybe (Left . NotInScope $ names a) pure $ ctx a
      u' <- maybe (Left . NotInScope $ names a) pure $ usages a
      case (u, u') of
        (Zero, _) -> pure (usages, Entry u' aTy)
        (One, Zero) -> Left $ UsingErased $ names a
        (One, One) ->
          pure (\x -> Zero <$ guard (x == a) <|> usages x, Entry u' aTy)
        (One, Many) -> pure (usages, Entry u' aTy)
        (Many, Zero) -> Left $ UsingErased $ names a
        (Many, One) ->
          pure (\x -> Zero <$ guard (x == a) <|> usages x, Entry u' aTy)
        (Many, Many) -> pure (usages, Entry u' aTy)
    Ann a u' b -> do
      _ <- checkZero depth names ctx usages b Type
      usages' <- check depth names ctx usages a u' b
      pure (usages', Entry u' b)
    App a b -> do
      (usages', Entry aUsage aTy) <- infer depth names ctx usages a u
      case aTy of
        Pi u' _ s t -> do
          let u'' = times u' aUsage
          usages'' <- check depth names ctx usages' b u'' s
          pure (usages'', Entry aUsage $ instantiate1 (Ann b u'' s) t)
        _ -> Left $ ExpectedPi $ names <$> aTy
    Fst a -> do
      (usages', Entry aUsage aTy) <- infer depth names ctx usages a u
      case aTy of
        With _ s _ -> pure (usages', Entry aUsage s)
        _ -> Left $ ExpectedWith $ names <$> aTy
    Snd a -> do
      (usages', Entry aUsage aTy) <- infer depth names ctx usages a u
      case aTy of
        With _ _ t -> pure (usages', Entry aUsage (instantiate1 (Fst a) t))
        _ -> Left $ ExpectedWith $ names <$> aTy
    _ -> Left $ Can'tInfer $ names <$> tm
