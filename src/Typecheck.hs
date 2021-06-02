{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

module Typecheck (
  Env (..),
  checkType,
  checkTerm,
  inferType,
  inferTerm,
) where

import Bound.Context (Context)
import qualified Bound.Context as Context
import Bound.Scope (fromScope, instantiate, instantiate1, toScope)
import Bound.Var (Var (..), unvar)
import Control.Lens.Getter (to, view, (^.))
import Control.Lens.Setter (mapped, over, (.~))
import Control.Lens.TH (makeLenses)
import Control.Lens.Tuple (_3)
import Data.Bool (bool)
import Data.Foldable (traverse_)
import Data.Function ((&))
import Data.List.NonEmpty (NonEmpty (..))
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Semiring (times)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.These (These (..))
import GHC.Stack (HasCallStack)

import Context
import Syntax
import TypeError
import Unify

data Env a l x = Env
  { _envDepth :: a -> x
  , _envNames :: x -> a
  , _envTypes :: x -> Maybe (Entry a l x)
  , _envUsages :: Context x Usage
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
    PVar _ -> instantiate (\case V -> foldl App f xs) v
    PCtor n _ count ->
      case f of
        Var n' ->
          if n' == depth n
            then
              if count == length xs
                then instantiate (\case C x -> xs !! x) v
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
    Tensor n u a b -> Tensor n u (eval depth a) (evalScope depth b)
    UnpackTensor m n a b ->
      case eval depth a of
        MkTensor x y -> eval depth $ instantiate (bool x y) b
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

unsafeGetUsage :: Ord a => a -> Context a b -> b
unsafeGetUsage a usages =
  case Context.lookup a usages of
    Nothing -> error "check: bound variable's usage was not found"
    Just u -> u

unsafeCheckConsumed ::
  Ord x =>
  -- | Variable names
  (x -> a) ->
  -- | Expected usage
  Usage ->
  -- | Variable
  x ->
  -- | Usages
  Context x Usage ->
  Either (TypeError l a) ()
unsafeCheckConsumed names u a usages =
  let u' = unsafeGetUsage a usages
   in case (u, u') of
        (One, One) -> Left $ UnusedLinear $ names a
        _ -> pure ()

mergeUsages ::
  Ord x =>
  Context x Usage ->
  Context x Usage ->
  Context x Usage
mergeUsages =
  Context.zipWithKey
    ( \_ ->
        \case
          These uA uB ->
            case (uA, uB) of
              (Zero, Zero) -> Just Zero
              (Zero, One) -> Just Zero
              (Zero, Many) -> error "mergeUsages: zero as many"
              (One, Zero) -> Just Zero
              (One, One) -> Just One
              (One, Many) -> error "mergeUsages: one as many"
              (Many, Zero) -> error "mergeUsages: many as zero"
              (Many, One) -> error "mergeUsages: many as one"
              (Many, Many) -> Just Many
          This _ ->
            Nothing
          That _ ->
            Nothing
    )

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
  (Ord b, Ord x) =>
  (b -> a) ->
  (b -> Maybe (Entry a l x)) ->
  Map b Usage ->
  Env a l x ->
  Env a l (Var b x)
deeperEnv names types usages env =
  Env
    { _envDepth = F . _envDepth env
    , _envNames = unvar names (_envNames env)
    , _envTypes = fmap (fmap F) . unvar types (_envTypes env)
    , _envUsages = Context.merge usages (_envUsages env)
    }

checkBranchesMatching ::
  (Ord x, Ord a) =>
  Usage ->
  Env a l x ->
  (Term a l x, Usage, Ty a l x) ->
  NonEmpty (Branch a (Term a l) x) ->
  Usage ->
  Ty a l x ->
  Map a (Term a l x) ->
  Maybe (Set a) ->
  Either (TypeError l a) (Context x Usage)
-- impossible branch for a non-inductive type is not allowed
checkBranchesMatching _ _ _ (BranchImpossible _ :| _) _ _ _ Nothing =
  Left NotImpossible
-- We are not matching on an inductive type
checkBranchesMatching varCost env (inTm, inUsage, inTy) (Branch p v :| bs) u outTy ctors Nothing =
  case p of
    PVar n -> do
      usages' <-
        check
          varCost
          ( deeperEnv
              (\V -> n)
              (const $ Just (BindingEntry inTy))
              (Map.singleton V inUsage)
              env
          )
          (fromScope v)
          u
          (F <$> outTy)
      unsafeCheckConsumed
        (unvar (\V -> n) (env ^. envNames))
        inUsage
        (B V)
        usages'
      case bs of
        [] ->
          let (_, usages'') = Context.split usages'
           in pure usages''
        bb : bbs -> checkBranchesMatching varCost env (inTm, inUsage, inTy) (bb :| bbs) u outTy ctors Nothing
    PCtor s _ _ -> Left $ NotConstructorFor s $ env ^. envNames <$> inTy
-- impossible branch for an inductive type. the match is impossible if the inductive type has no constructors,
-- or if the type of the scrutinee is incompatible with with the constructor's output
checkBranchesMatching varCost env (inTm, inUsage, inTy) (BranchImpossible p :| bs) u outTy allCtors (Just remaining) =
  case p of
    PVar _ ->
      if Map.null allCtors
        then case bs of
          [] -> pure $ env ^. envUsages
          bb : bbs ->
            checkBranchesMatching varCost env (inTm, inUsage, inTy) (bb :| bbs) u outTy allCtors (Just remaining)
        else Left NotImpossible
    PCtor ctorName ns _ -> do
      ctorTy <-
        case Map.lookup ctorName allCtors of
          Nothing ->
            Left . NotConstructorFor ctorName $ env ^. envNames <$> inTy
          Just res -> pure res
      (_, retTy) <- applyCtorArgs (env ^. envDepth) ctorName ctorTy ns
      case unifyInductive (env ^. envNames) (env ^. envNames) (env ^. envTypes) inTy retTy of
        Right{} -> Left NotImpossible
        Left{} ->
          case bs of
            [] -> pure $ env ^. envUsages
            bb : bbs ->
              checkBranchesMatching varCost env (inTm, inUsage, inTy) (bb :| bbs) u outTy allCtors (Just remaining)
-- We are matching on an inductive type, and cases remain for `ctors`
checkBranchesMatching varCost env (inTm, inUsage, inTy) (Branch p v :| bs) u outTy allCtors (Just remaining) =
  case p of
    PVar n -> do
      usages' <-
        check
          varCost
          ( deeperEnv
              (\V -> n)
              (const $ Just (BindingEntry inTy))
              (Map.singleton V inUsage)
              env
          )
          (fromScope v)
          u
          (fmap F $ outTy >>= matchSubst inTm (Var $ (env ^. envDepth) n))
      unsafeCheckConsumed (unvar (\V -> n) $ env ^. envNames) inUsage (B V) usages'
      case bs of
        [] ->
          let (_, usages'') = Context.split usages'
           in pure usages''
        bb : bbs ->
          -- The match is now total
          checkBranchesMatching varCost env (inTm, inUsage, inTy) (bb :| bbs) u outTy allCtors (Just mempty)
    PCtor ctorName ns _ -> do
      ctorTy <-
        case Map.lookup ctorName allCtors of
          Nothing -> Left . NotConstructorFor ctorName $ env ^. envNames <$> inTy
          Just res -> pure res
      (args, retTy) <- applyCtorArgs (env ^. envDepth) ctorName ctorTy ns
      let (argUsages, argTys) = unzip args
      subst <- unifyInductive (env ^. envNames) (env ^. envNames) (env ^. envTypes) inTy retTy
      usages' <-
        check
          varCost
          ( deeperEnv
              (\(C ix) -> ns !! ix)
              (Just . BindingEntry . (argTys !!) . pathVal)
              (Map.fromList $ zipWith (\ix argUsage -> (C ix, times inUsage argUsage)) [0 ..] argUsages)
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
        ( \(_, ix) ->
            unsafeCheckConsumed
              (unvar (pathArgName p) $ env ^. envNames)
              (times inUsage $ argUsages !! ix)
              (B $ C ix)
              usages'
        )
        (zip ns [0 ..])
      let remaining' = Set.delete ctorName remaining
      case bs of
        [] ->
          if Set.null remaining'
            then
              let (_, usages'') = Context.split usages'
               in pure usages''
            else Left $ UnmatchedCases remaining
        bb : bbs ->
          checkBranchesMatching
            varCost
            env
            (inTm, inUsage, inTy)
            (bb :| bbs)
            u
            outTy
            allCtors
            (Just remaining')

checkBranches ::
  (Ord x, Ord a) =>
  Usage ->
  Env a l x ->
  (Term a l x, Usage, Ty a l x) ->
  NonEmpty (Branch a (Term a l) x) ->
  Usage ->
  Ty a l x ->
  Either (TypeError l a) (Context x Usage)
checkBranches varCost env (inTm, inUsage, inTy) bs u outTy = do
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
    varCost
    env
    (inTm, inUsage, inTy)
    bs
    u
    outTy
    (fromMaybe mempty mustMatch)
    (Map.keysSet <$> mustMatch)
 where
  (inTyCon, _) = unfoldApps inTy

check ::
  HasCallStack =>
  (Ord x, Ord a) =>
  Usage ->
  Env a l x ->
  Term a l x ->
  Usage ->
  Ty a l x ->
  Either (TypeError l a) (Context x Usage)
check _ _ _ Many _ = error "check called with usage Many"
check varCost env tm u ty_ =
  let ty = eval (env ^. envDepth) ty_ -- pre-compute
   in case tm of
        Type ->
          case ty of
            Type -> pure $ env ^. envUsages
            _ -> Left $ ExpectedType $ env ^. envNames <$> ty
        Pi _ n a b ->
          case ty of
            Type -> do
              _ <- checkType env a Type
              _ <-
                checkType
                  ( deeperEnv
                      (const n)
                      (const (Just $ BindingEntry a))
                      (Map.singleton () Zero)
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
                  varCost
                  ( deeperEnv
                      (const n)
                      (const (Just $ BindingEntry s))
                      (Map.singleton () (times u' u))
                      env
                  )
                  (fromScope a)
                  u
                  (fromScope t)
              unsafeCheckConsumed
                (unvar (const n) $ env ^. envNames)
                (times u' u)
                (B ())
                usages'
              let (_, usages'') = Context.split usages'
              pure usages''
            _ -> Left $ ExpectedPi $ env ^. envNames <$> ty
        Tensor n _ a b ->
          case ty of
            Type -> do
              _ <- checkType env a Type
              _ <-
                checkType
                  ( deeperEnv
                      (const n)
                      (const (Just $ BindingEntry a))
                      (Map.singleton () Zero)
                      env
                  )
                  (fromScope b)
                  Type
              pure $ env ^. envUsages
            _ -> Left $ ExpectedType $ env ^. envNames <$> ty
        MkTensor a b ->
          case ty of
            Tensor _ u' s t -> do
              usages' <- check (times varCost u') env a u s
              check varCost (env & envUsages .~ usages') b u (instantiate1 (Ann a u s) t)
            _ -> Left $ ExpectedTensor $ env ^. envNames <$> ty
        UnpackTensor n1 n2 a b -> do
          (usages', _, aTy) <- infer varCost env a u
          case aTy of
            Tensor _ u' s t -> do
              let aUsage = times u u'
              usages'' <-
                check
                  varCost
                  ( deeperEnv
                      (bool n1 n2)
                      (Just . BindingEntry . bool s (instantiate1 (Fst a) t))
                      (Map.fromList [(False, aUsage), (True, u)])
                      (env & envUsages .~ usages')
                  )
                  (fromScope b)
                  u
                  (F <$> ty)
              let names' = unvar (bool n1 n2) $ env ^. envNames
              unsafeCheckConsumed names' aUsage (B False) usages''
              unsafeCheckConsumed names' u (B True) usages''
              let (_, usages''') = Context.split usages''
              pure usages'''
            _ -> Left $ ExpectedTensor $ env ^. envNames <$> aTy
        With n a b ->
          case ty of
            Type -> do
              _ <- checkType env a Type
              _ <-
                checkType
                  ( deeperEnv
                      (const n)
                      (const (Just $ BindingEntry a))
                      (Map.singleton () Zero)
                      env
                  )
                  (fromScope b)
                  Type
              pure $ env ^. envUsages
            _ -> Left $ ExpectedType $ env ^. envNames <$> ty
        MkWith a b ->
          case ty of
            With _ s t -> do
              usagesA <- check varCost env a u s
              usagesB <- check varCost env b u (instantiate1 (Ann a u s) t)
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
          (usages', usage, aTy) <- infer varCost env a u
          checkBranches varCost (env & envUsages .~ usages') (a, usage, aTy) bs u ty
        _ -> do
          (usages', _, tmTy) <- infer varCost env tm u
          if tmTy == ty
            then pure usages'
            else Left $ TypeMismatch (env ^. envNames <$> ty) (env ^. envNames <$> tmTy)

checkType ::
  (Ord x, Ord a) =>
  Env a l x ->
  Term a l x ->
  Ty a l x ->
  Either (TypeError l a) (Context x Usage)
checkType env tm =
  check Zero (env & envUsages . mapped .~ Zero) tm Zero

checkTerm ::
  (Ord x, Ord a) =>
  Env a l x ->
  Term a l x ->
  Ty a l x ->
  Either (TypeError l a) (Context x Usage)
checkTerm env tm = check One env tm One

infer ::
  HasCallStack =>
  (Ord x, Ord a) =>
  Usage ->
  Env a l x ->
  Term a l x ->
  Usage ->
  Either (TypeError l a) (Context x Usage, Usage, Ty a l x)
infer _ _ _ Many = error "infer called with usage Many"
infer varCost env tm u =
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
            (view (envUsages . to (flip Context.lookup)) env a)
        case (varCost, u') of
          (Zero, _) -> pure (env ^. envUsages, u', aTy)
          (One, Zero) -> Left $ UsingErased $ view envNames env a
          (One, One) ->
            pure (Context.insert a Zero (view envUsages env), u', aTy)
          (One, Many) -> pure (env ^. envUsages, u', aTy)
          (Many, Zero) -> Left $ UsingErased $ view envNames env a
          (Many, One) -> Left $ OverusedLinear $ view envNames env a
          (Many, Many) -> pure (env ^. envUsages, u', aTy)
      Ann a u' b -> do
        _ <- checkType env b Type
        usages' <- check varCost env a u' b
        pure (usages', u', b)
      App a b -> do
        (usages', _, aTy) <- infer varCost env a u
        case aTy of
          Pi u' _ s t -> do
            let u'' = if u == Zero || u' == Zero then Zero else One
            usages'' <- check (times varCost u') (env & envUsages .~ usages') b u'' s
            pure (usages'', u, instantiate1 (Ann b u'' s) t)
          _ -> Left $ ExpectedPi $ env ^. envNames <$> aTy
      Fst a -> do
        (usages', _, aTy) <- infer varCost env a u
        case aTy of
          With _ s _ -> pure (usages', u, s)
          _ -> Left $ ExpectedWith $ env ^. envNames <$> aTy
      Snd a -> do
        (usages', _, aTy) <- infer varCost env a u
        case aTy of
          With _ _ t -> pure (usages', u, instantiate1 (Fst a) t)
          _ -> Left $ ExpectedWith $ env ^. envNames <$> aTy
      _ -> Left $ Can'tInfer $ env ^. envNames <$> tm

inferType ::
  HasCallStack =>
  (Ord x, Ord a) =>
  Env a l x ->
  Term a l x ->
  Either (TypeError l a) (Context x Usage, Usage, Ty a l x)
inferType env tm = infer Zero (env & envUsages . mapped .~ Zero) tm Zero

inferTerm ::
  HasCallStack =>
  (Ord x, Ord a) =>
  Env a l x ->
  Term a l x ->
  Either (TypeError l a) (Context x Usage, Usage, Ty a l x)
inferTerm env tm = infer One env tm One