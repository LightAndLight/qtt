{-# language DeriveFunctor #-}
{-# language EmptyCase #-}
{-# language FlexibleContexts #-}
{-# language GADTs #-}
{-# language LambdaCase #-}
{-# language TemplateHaskell #-}
module Typecheck where

import Bound.Name (Name(..), instantiateName, instantiate1Name)
import Bound.Scope (fromScope, toScope, instantiate1)
import Bound.Var (Var(..), unvar)
import Control.Applicative ((<|>))
import Control.Comonad (extract)
import Control.Lens.Setter (over, mapped)
import Control.Lens.Tuple (_3)
import Control.Lens.TH (makeLenses)
import Control.Monad (guard)
import Data.Bool (bool)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Semiring (times)

import qualified Bound.Name as Bound

import Syntax

data Entry n l a
  = InductiveEntry { _entryType :: Ty n l a, _entryCtors :: [(n, Term n l a)] }
  | BindingEntry { _entryType :: Ty n l a }
  deriving (Eq, Show, Functor)
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

pickBranch ::
  Eq x =>
  (a -> x) ->
  Term a l x ->
  [Term a l x] ->
  NonEmpty (Branch a (Term a l) x) ->
  Term a l x
pickBranch depth f xs (Branch p v :| bs) =
  case p of
    PVar _ -> instantiateName (\case; V -> foldl App f xs) v
    PCtor n _ count ->
      case f of
        Var n' ->
          if n' == depth n
          then
            if count == length xs
            then instantiateName (\case; C x -> xs !! x) v
            else error "pickBranch: incorrect number of arguments to constructor"
          else
            case bs of
              [] -> error "pickBranch: no brach to take"
              bb:bbs -> pickBranch depth f xs (bb :| bbs)
        _ -> error "pickBranch: can't match on non-var"
    PWild -> instantiateName (\case {}) v

eval :: Eq x => (a -> x) -> Term a l x -> Term a l x
eval depth tm =
  case tm of
    Loc _ a -> eval depth a
    Var a -> Var a
    Ann a _ _ -> a
    Type -> Type
    Lam n a -> Lam n $ evalScope depth a
    Pi u n a b -> Pi u n (eval depth a) (evalScope depth b)
    App a b ->
      case eval depth a of
        Lam _ s -> eval depth $ instantiate1 b s
        a' -> App a' $ eval depth b
    MkTensor a b -> MkTensor (eval depth a) (eval depth b)
    Tensor n a b -> Tensor n (eval depth a) (evalScope depth b)
    UnpackTensor m n a b ->
      case eval depth a of
        MkTensor x y -> eval depth $ instantiateName (bool x y) b
        a' -> UnpackTensor m n a' $ evalScope depth b
    MkWith a b -> MkWith (eval depth a) (eval depth b)
    With n a b -> With n (eval depth a) (evalScope depth b)
    Fst a ->
      case eval depth a of
        MkWith x _ -> x
        a' -> Fst a'
    Snd a ->
      case eval depth a of
        MkWith _ y -> y
        a' -> Snd a'
    Unit -> Unit
    MkUnit -> MkUnit
    Case a bs -> let (f, xs) = unfoldApps (eval depth a) in pickBranch depth f xs bs
  where
    evalScope d = toScope . eval (F . d) . fromScope

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

checkBranchesMatching ::
  (Eq x, Eq a) =>
  (a -> x) ->
  (x -> a) ->
  (x -> Maybe (Entry a l x)) ->
  (x -> Maybe Usage) ->
  (Usage, Ty a l x) ->
  NonEmpty (Branch a (Term a l) x) ->
  Usage ->
  Ty a l x ->
  Maybe [(a, Term a l x)] ->
  Either (TypeError l a) (x -> Maybe Usage)
checkBranchesMatching depth names ctx usages inTy (Branch p v :| bs) u outTy Nothing =
  case p of
    PVar n -> _
    PCtor s ns n -> _
    PWild -> _
checkBranchesMatching depth names ctx usages inTy bs u outTy (Just ctors) = _

checkBranches ::
  (Eq x, Eq a) =>
  (a -> x) ->
  (x -> a) ->
  (x -> Maybe (Entry a l x)) ->
  (x -> Maybe Usage) ->
  (Usage, Ty a l x) ->
  NonEmpty (Branch a (Term a l) x) ->
  Usage ->
  Ty a l x ->
  Either (TypeError l a) (x -> Maybe Usage)
checkBranches depth names ctx usages (inUsage, inTy) bs u outTy = do
  mustMatch <-
    case inTyCon of
      Var c -> do
        cEntry <- maybe (Left $ NotInScope $ names c) pure $ ctx c
        pure $
          case cEntry of
            InductiveEntry _ ctors -> Just ctors
            _ -> Nothing
      _ -> Right Nothing
  checkBranchesMatching depth names ctx usages (inUsage, inTy) bs u outTy mustMatch
  where
    (inTyCon, _) = unfoldApps inTy

checkZero ::
  (Eq x, Eq a) =>
  (a -> x) ->
  (x -> a) ->
  (x -> Maybe (Entry a l x)) ->
  (x -> Maybe Usage) ->
  Term a l x ->
  Ty a l x ->
  Either (TypeError l a) (x -> Maybe Usage)
checkZero depth names ctx usages tm =
  check depth names ctx ((Zero <$) . usages) tm Zero . eval depth

check ::
  (Eq x, Eq a) =>
  (a -> x) ->
  (x -> a) ->
  (x -> Maybe (Entry a l x)) ->
  (x -> Maybe Usage) ->
  Term a l x ->
  Usage ->
  Ty a l x ->
  Either (TypeError l a) (x -> Maybe Usage)
check depth names ctx usages tm u ty_ =
  let ty = eval depth ty_ in -- pre-compute
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
              (fmap (fmap F) . unvar (const (Just $ BindingEntry a) . extract) ctx)
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
              (fmap (fmap F) . unvar (const (Just $ BindingEntry s) . extract) ctx)
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
              (fmap (fmap F) . unvar (const (Just $ BindingEntry a) . extract) ctx)
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
      (usages', aUsage, aTy) <- infer depth names ctx usages a u
      case aTy of
        Tensor _ s t -> do
          let names' = unvar Bound.name names
          usages'' <-
            check
              (F . depth)
              names'
              (fmap (fmap F) . unvar (Just . BindingEntry . bool s (instantiate1Name (Fst a) t) . extract) ctx)
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
              (fmap (fmap F) . unvar (const (Just $ BindingEntry a)) ctx)
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
    Case a bs -> do
      (usages', usage, aTy) <- infer depth names ctx usages a u
      checkBranches depth names ctx usages' (usage, aTy) bs u ty
    _ -> do
      (usages', _, tmTy) <- infer depth names ctx usages tm u
      if tmTy == ty
        then pure usages'
        else Left $ TypeMismatch (names <$> ty) (names <$> tmTy)

infer ::
  (Eq a, Eq x) =>
  (a -> x) ->
  (x -> a) ->
  (x -> Maybe (Entry a l x)) ->
  (x -> Maybe Usage) ->
  Term a l x ->
  Usage ->
  Either (TypeError l a) (x -> Maybe Usage, Usage, Ty a l x)
infer depth names ctx usages tm u =
  over (mapped._3) (eval depth) $ -- post compute
  case tm of
    Var a -> do
      aTy <- maybe (Left . NotInScope $ names a) (pure . _entryType) $ ctx a
      u' <- maybe (Left . NotInScope $ names a) pure $ usages a
      case (u, u') of
        (Zero, _) -> pure (usages, u', aTy)
        (One, Zero) -> Left $ UsingErased $ names a
        (One, One) ->
          pure (\x -> Zero <$ guard (x == a) <|> usages x, u', aTy)
        (One, Many) -> pure (usages, u', aTy)
        (Many, Zero) -> Left $ UsingErased $ names a
        (Many, One) ->
          pure (\x -> Zero <$ guard (x == a) <|> usages x, u', aTy)
        (Many, Many) -> pure (usages, u', aTy)
    Ann a u' b -> do
      _ <- checkZero depth names ctx usages b Type
      usages' <- check depth names ctx usages a u' b
      pure (usages', u', b)
    App a b -> do
      (usages', aUsage, aTy) <- infer depth names ctx usages a u
      case aTy of
        Pi u' _ s t -> do
          let u'' = times u' aUsage
          usages'' <- check depth names ctx usages' b u'' s
          pure (usages'', aUsage, instantiate1 (Ann b u'' s) t)
        _ -> Left $ ExpectedPi $ names <$> aTy
    Fst a -> do
      (usages', aUsage, aTy) <- infer depth names ctx usages a u
      case aTy of
        With _ s _ -> pure (usages', aUsage, s)
        _ -> Left $ ExpectedWith $ names <$> aTy
    Snd a -> do
      (usages', aUsage, aTy) <- infer depth names ctx usages a u
      case aTy of
        With _ _ t -> pure (usages', aUsage, instantiate1 (Fst a) t)
        _ -> Left $ ExpectedWith $ names <$> aTy
    _ -> Left $ Can'tInfer $ names <$> tm
