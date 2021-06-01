{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

module Typecheck where

import Bound.Name (Name (..), instantiate1Name, instantiateName)
import Bound.Scope (fromScope, instantiate1, toScope)
import Bound.Var (Var (..), unvar)
import Control.Applicative ((<|>))
import Control.Comonad (extract)
import Control.Lens.Getter (view, (^.))
import Control.Lens.Setter (mapped, over, (%~), (.~))
import Control.Lens.TH (makeLenses)
import Control.Lens.Tuple (_3)
import Control.Monad (guard)
import Data.Bool (bool)
import Data.Foldable (traverse_)
import Data.Function ((&))
import Data.List.NonEmpty (NonEmpty (..))
import Data.Map (Map)
import Data.Maybe (fromMaybe)
import Data.Semiring (times)
import Data.Set (Set)

import qualified Bound.Name as Bound
import qualified Data.Map as Map
import qualified Data.Set as Set

import Context
import Syntax
import TypeError
import Unify

data Env a l x = Env
  { _envDepth :: a -> x
  , _envNames :: x -> a
  , _envTypes :: x -> Maybe (Entry a l x)
  , _envUsages :: x -> Maybe Usage
  }
makeLenses ''Env

pickBranch ::
  Eq x =>
  (a -> x) ->
  Term a l x ->
  [Term a l x] ->
  NonEmpty (Branch a (Term a l) x) ->
  Term a l x
pickBranch depth f xs (BranchImpossible _ :| bs) =
  case bs of
    [] -> error "pickBranch: no brach to take"
    bb : bbs -> pickBranch depth f xs (bb :| bbs)
pickBranch depth f xs (Branch p v :| bs) =
  case p of
    PVar _ -> instantiateName (\case V -> foldl App f xs) v
    PCtor n _ count ->
      case f of
        Var n' ->
          if n' == depth n
            then
              if count == length xs
                then instantiateName (\case C x -> xs !! x) v
                else error "pickBranch: incorrect number of arguments to constructor"
            else case bs of
              [] -> error "pickBranch: no brach to take"
              bb : bbs -> pickBranch depth f xs (bb :| bbs)
        _ -> error "pickBranch: can't match on non-var"

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
  -- | Variable names
  (x -> a) ->
  -- | Expected usage
  Usage ->
  -- | Variable
  x ->
  -- | Usages
  (x -> Maybe Usage) ->
  Either (TypeError l a) ()
unsafeCheckConsumed names u a usages =
  let u' = unsafeGetUsage a usages
   in case (u, u') of
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

{- | Apply a list of arguments to a function, throwing an error
 if the function cannot be fully applied
-}
applyCtorArgs ::
  forall a l x.
  -- | Depth
  (a -> x) ->
  -- | Constructor name
  a ->
  -- | Constructor type
  Ty a l x ->
  -- | Arg names
  [a] ->
  Either
    (TypeError l a)
    -- ([Ty a l (Var (Name a (Path Int)) x)], Ty a l (Var (Name a (Path Int)) x))
    ([(Usage, Ty a l x)], Ty a l x)
applyCtorArgs depth ctorName = go id 0
 where
  go ::
    forall y.
    -- (y -> Var (Name a (Path Int)) x) ->
    (y -> x) ->
    -- | Current arg
    Int ->
    -- | Constructor type
    Ty a l y ->
    -- | Arg names
    [a] ->
    Either
      (TypeError l a)
      ([(Usage, Ty a l x)], Ty a l x)
  go _ !_ Pi{} [] = Left $ NotEnoughArguments ctorName
  go f !_ ctorTy [] = Right ([], f <$> ctorTy)
  go f !count (Pi u _ s t) (a : as) = do
    (tys, ret) <-
      go
        (unvar (depth . const a) f)
        (count + 1)
        (fromScope t)
        as
    pure ((u, fmap f s) : tys, ret)
  go _ !_ _ (_ : _) = Left $ TooManyArguments ctorName

matchSubst :: Eq a => Term n l a -> Term n l a -> a -> Term n l a
matchSubst inTm t =
  case inTm of
    Var v -> \x -> if x == v then t else pure x
    _ -> pure

deeperEnv ::
  (b -> a) ->
  (b -> Maybe (Entry a l x)) ->
  (b -> Maybe Usage) ->
  Env a l x ->
  Env a l (Var b x)
deeperEnv names types usages env =
  Env
    { _envDepth = F . _envDepth env
    , _envNames = unvar names (_envNames env)
    , _envTypes = fmap (fmap F) . unvar types (_envTypes env)
    , _envUsages = unvar usages (_envUsages env)
    }

checkBranchesMatching ::
  (Ord x, Ord a) =>
  Env a l x ->
  (Term a l x, Usage, Ty a l x) ->
  NonEmpty (Branch a (Term a l) x) ->
  Usage ->
  Ty a l x ->
  Map a (Term a l x) ->
  Maybe (Set a) ->
  Either (TypeError l a) (x -> Maybe Usage)
-- impossible branch for a non-inductive type is not allowed
checkBranchesMatching _ _ (BranchImpossible _ :| _) _ _ _ Nothing =
  Left NotImpossible
-- We are not matching on an inductive type
checkBranchesMatching env (inTm, inUsage, inTy) (Branch p v :| bs) u outTy ctors Nothing =
  case p of
    PVar n -> do
      usages' <-
        check
          ( deeperEnv
              Bound.name
              (const $ Just (BindingEntry inTy))
              (const $ Just inUsage)
              env
          )
          (fromScope v)
          u
          (F <$> outTy)
      unsafeCheckConsumed
        (unvar Bound.name (env ^. envNames))
        inUsage
        (B $ Name n V)
        usages'
      case bs of
        [] -> pure $ usages' . F
        bb : bbs -> checkBranchesMatching env (inTm, inUsage, inTy) (bb :| bbs) u outTy ctors Nothing
    PCtor s _ _ -> Left $ NotConstructorFor s $ env ^. envNames <$> inTy
-- impossible branch for an inductive type. the match is impossible if the inductive type has no constructors,
-- or if the type of the scrutinee is incompatible with with the constructor's output
checkBranchesMatching env (inTm, inUsage, inTy) (BranchImpossible p :| bs) u outTy allCtors (Just remaining) =
  case p of
    PVar _ ->
      if Map.null allCtors
        then case bs of
          [] -> pure $ env ^. envUsages
          bb : bbs ->
            checkBranchesMatching env (inTm, inUsage, inTy) (bb :| bbs) u outTy allCtors (Just remaining)
        else Left NotImpossible
    PCtor ctorName ns _ -> do
      ctorTy <-
        case Map.lookup ctorName allCtors of
          Nothing ->
            Left . NotConstructorFor ctorName $ env ^. envNames <$> inTy
          Just res -> pure res
      (_, retTy) <- applyCtorArgs (env ^. envDepth) ctorName ctorTy ns
      case unifyInductive (env ^. envNames) (env ^. envTypes) inTy retTy of
        Right{} -> Left NotImpossible
        Left{} ->
          case bs of
            [] -> pure $ env ^. envUsages
            bb : bbs ->
              checkBranchesMatching env (inTm, inUsage, inTy) (bb :| bbs) u outTy allCtors (Just remaining)
-- We are matching on an inductive type, and cases remain for `ctors`
checkBranchesMatching env (inTm, inUsage, inTy) (Branch p v :| bs) u outTy allCtors (Just remaining) =
  case p of
    PVar n -> do
      usages' <-
        check
          ( deeperEnv
              Bound.name
              (const $ Just (BindingEntry inTy))
              (const $ Just inUsage)
              env
          )
          (fromScope v)
          u
          (fmap F $ outTy >>= matchSubst inTm (Var $ (env ^. envDepth) n))
      unsafeCheckConsumed (unvar Bound.name $ env ^. envNames) inUsage (B $ Name n V) usages'
      case bs of
        [] -> pure $ usages' . F
        bb : bbs ->
          -- The match is now total
          checkBranchesMatching env (inTm, inUsage, inTy) (bb :| bbs) u outTy allCtors (Just mempty)
    PCtor ctorName ns _ -> do
      ctorTy <-
        case Map.lookup ctorName allCtors of
          Nothing -> Left . NotConstructorFor ctorName $ env ^. envNames <$> inTy
          Just res -> pure res
      (args, retTy) <- applyCtorArgs (env ^. envDepth) ctorName ctorTy ns
      let (argUsages, argTys) = unzip args
      subst <- unifyInductive (env ^. envNames) (env ^. envTypes) inTy retTy
      usages' <-
        check
          ( deeperEnv
              Bound.name
              (Just . BindingEntry . (argTys !!) . pathVal . extract)
              (Just . times inUsage . (argUsages !!) . pathVal . extract)
              env
          )
          (fromScope v)
          u
          ( fmap F . bindSubst subst $
              outTy
                >>= matchSubst
                  inTm
                  ( foldl
                      (\b a -> App b (Var $ (env ^. envDepth) a))
                      (Var $ (env ^. envDepth) ctorName)
                      ns
                  )
          )
      traverse_
        ( \(n, ix) ->
            unsafeCheckConsumed
              (unvar Bound.name $ env ^. envNames)
              (times inUsage $ argUsages !! ix)
              (B $ Name n (C ix))
              usages'
        )
        (zip ns [0 ..])
      let remaining' = Set.delete ctorName remaining
      case bs of
        [] ->
          if Set.null remaining'
            then pure (usages' . F)
            else Left $ UnmatchedCases remaining
        bb : bbs ->
          checkBranchesMatching
            env
            (inTm, inUsage, inTy)
            (bb :| bbs)
            u
            outTy
            allCtors
            (Just remaining')

checkBranches ::
  (Ord x, Ord a) =>
  Env a l x ->
  (Term a l x, Usage, Ty a l x) ->
  NonEmpty (Branch a (Term a l) x) ->
  Usage ->
  Ty a l x ->
  Either (TypeError l a) (x -> Maybe Usage)
checkBranches env (inTm, inUsage, inTy) bs u outTy = do
  mustMatch <-
    case inTyCon of
      Var c -> do
        cEntry <-
          maybe
            (Left $ NotInScope $ view envNames env c)
            pure
            (view envTypes env c)
        pure $
          case cEntry of
            InductiveEntry _ ctors -> Just ctors
            _ -> Nothing
      _ -> Right Nothing
  checkBranchesMatching
    env
    (inTm, inUsage, inTy)
    bs
    u
    outTy
    (fromMaybe mempty mustMatch)
    (Map.keysSet <$> mustMatch)
 where
  (inTyCon, _) = unfoldApps inTy

checkZero ::
  (Ord x, Ord a) =>
  Env a l x ->
  Term a l x ->
  Ty a l x ->
  Either (TypeError l a) (x -> Maybe Usage)
checkZero env tm =
  check (env & envUsages %~ ((Zero <$) .)) tm Zero . eval (env ^. envDepth)

check ::
  (Ord x, Ord a) =>
  Env a l x ->
  Term a l x ->
  Usage ->
  Ty a l x ->
  Either (TypeError l a) (x -> Maybe Usage)
check env tm u ty_ =
  let ty = eval (env ^. envDepth) ty_ -- pre-compute
   in case tm of
        Type ->
          case ty of
            Type -> pure $ env ^. envUsages
            _ -> Left $ ExpectedType $ env ^. envNames <$> ty
        Pi _ _ a b ->
          case ty of
            Type -> do
              _ <- checkZero env a Type
              _ <-
                checkZero
                  ( deeperEnv
                      Bound.name
                      (const (Just $ BindingEntry a) . extract)
                      (const (Just Zero) . extract)
                      env
                  )
                  (fromScope b)
                  Type
              pure $ env ^. envUsages
            _ -> Left $ ExpectedType $ env ^. envNames <$> ty
        Lam n a ->
          case ty of
            Pi u' _ s t -> do
              usages' <-
                check
                  ( deeperEnv
                      Bound.name
                      (const (Just $ BindingEntry s) . extract)
                      (const (Just $ times u' u))
                      env
                  )
                  (fromScope a)
                  u
                  (fromScope t)
              unsafeCheckConsumed
                (unvar Bound.name $ env ^. envNames)
                (times u' u)
                (B $ Name n ())
                usages'
              pure $ usages' . F
            _ -> Left $ ExpectedPi $ env ^. envNames <$> ty
        Tensor _ a b ->
          case ty of
            Type -> do
              _ <- checkZero env a Type
              _ <-
                checkZero
                  ( deeperEnv
                      Bound.name
                      (const (Just $ BindingEntry a) . extract)
                      (const (Just Zero) . extract)
                      env
                  )
                  (fromScope b)
                  Type
              pure $ env ^. envUsages
            _ -> Left $ ExpectedType $ env ^. envNames <$> ty
        MkTensor a b ->
          case ty of
            Tensor _ s t -> do
              usages' <- check env a u s
              check (env & envUsages .~ usages') b u (instantiate1 (Ann a u s) t)
            _ -> Left $ ExpectedTensor $ env ^. envNames <$> ty
        UnpackTensor n1 n2 a b -> do
          (usages', aUsage, aTy) <- infer env a u
          case aTy of
            Tensor _ s t -> do
              usages'' <-
                check
                  ( deeperEnv
                      Bound.name
                      (Just . BindingEntry . bool s (instantiate1Name (Fst a) t) . extract)
                      (const (Just aUsage) . extract)
                      (env & envUsages .~ usages')
                  )
                  (fromScope b)
                  u
                  (F <$> ty)
              let names' = unvar Bound.name $ env ^. envNames
              unsafeCheckConsumed names' aUsage (B $ Name n1 False) usages''
              unsafeCheckConsumed names' aUsage (B $ Name n2 True) usages''
              pure $ usages'' . F
            _ -> Left $ ExpectedTensor $ env ^. envNames <$> aTy
        With _ a b ->
          case ty of
            Type -> do
              _ <- checkZero env a Type
              _ <-
                checkZero
                  ( deeperEnv
                      Bound.name
                      (const (Just $ BindingEntry a))
                      (const (Just Zero))
                      env
                  )
                  (fromScope b)
                  Type
              pure $ env ^. envUsages
            _ -> Left $ ExpectedType $ env ^. envNames <$> ty
        MkWith a b ->
          case ty of
            With _ s t -> do
              usagesA <- check env a u s
              usagesB <- check env b u (instantiate1 (Ann a u s) t)
              pure $ mergeUsages usagesA usagesB
            _ -> Left $ ExpectedWith $ env ^. envNames <$> ty
        Unit ->
          case ty of
            Type -> pure $ env ^. envUsages
            _ -> Left $ ExpectedType $ env ^. envNames <$> ty
        MkUnit ->
          case ty of
            Unit -> pure $ env ^. envUsages
            _ -> Left $ ExpectedUnit $ env ^. envNames <$> ty
        Case a bs -> do
          (usages', usage, aTy) <- infer env a u
          checkBranches (env & envUsages .~ usages') (a, usage, aTy) bs u ty
        _ -> do
          (usages', _, tmTy) <- infer env tm u
          if tmTy == ty
            then pure usages'
            else Left $ TypeMismatch (env ^. envNames <$> ty) (env ^. envNames <$> tmTy)

infer ::
  (Ord x, Ord a) =>
  Env a l x ->
  Term a l x ->
  Usage ->
  Either (TypeError l a) (x -> Maybe Usage, Usage, Ty a l x)
infer env tm u =
  over (mapped . _3) (eval $ env ^. envDepth) $ -- post compute
    case tm of
      Var a -> do
        aTy <-
          maybe
            (Left . NotInScope $ view envNames env a)
            (pure . _entryType)
            (view envTypes env a)
        u' <-
          maybe
            (Left . NotInScope $ view envNames env a)
            pure
            (view envUsages env a)
        case (u, u') of
          (Zero, _) -> pure (env ^. envUsages, u', aTy)
          (One, Zero) -> Left $ UsingErased $ view envNames env a
          (One, One) ->
            pure (\x -> Zero <$ guard (x == a) <|> view envUsages env x, u', aTy)
          (One, Many) -> pure (env ^. envUsages, u', aTy)
          (Many, Zero) -> Left $ UsingErased $ view envNames env a
          (Many, One) ->
            pure (\x -> Zero <$ guard (x == a) <|> view envUsages env x, u', aTy)
          (Many, Many) -> pure (env ^. envUsages, u', aTy)
      Ann a u' b -> do
        _ <- checkZero env b Type
        usages' <- check env a u' b
        pure (usages', u', b)
      App a b -> do
        (usages', _, aTy) <- infer env a u
        case aTy of
          Pi u' _ s t -> do
            let u'' = times u u'
            usages'' <- check (env & envUsages .~ usages') b u'' s
            pure (usages'', u, instantiate1 (Ann b u'' s) t)
          _ -> Left $ ExpectedPi $ env ^. envNames <$> aTy
      Fst a -> do
        (usages', _, aTy) <- infer env a u
        case aTy of
          With _ s _ -> pure (usages', u, s)
          _ -> Left $ ExpectedWith $ env ^. envNames <$> aTy
      Snd a -> do
        (usages', _, aTy) <- infer env a u
        case aTy of
          With _ _ t -> pure (usages', u, instantiate1 (Fst a) t)
          _ -> Left $ ExpectedWith $ env ^. envNames <$> aTy
      _ -> Left $ Can'tInfer $ env ^. envNames <$> tm
