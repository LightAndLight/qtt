{-# language ScopedTypeVariables #-}
module Inductive where

import Bound.Scope (fromScope)
import Bound.Var (Var(..))
import Control.Monad (unless)
import Control.Monad.Writer.Strict (runWriter, tell)
import Data.Foldable (for_)

import Syntax
import Typecheck

data Inductive c a
  = Inductive
  { _indTypeName :: a
  , _indTypeType :: Term c a
  , _indConstructors :: [(c, Term c a)]
  } deriving (Eq, Show)

data InductiveError c a
  = IndTypeError a (TypeError c a a)
  | IndIncorrectType c
  | IndNotStrictlyPositive c
  deriving (Eq, Show)

returnsCtor :: forall c a. Eq a => Term c a -> a -> Bool
returnsCtor = go id
  where
    go :: forall x. Eq x => (a -> x) -> Term c x -> a -> Bool
    go ctx (Pi _ _ rest) val = go (F . ctx) (fromScope rest) val
    go ctx (App a _) val = go ctx a val
    go ctx (Var a) val = a == ctx val
    go _ _ _ = False

strictlyPositiveIn :: forall c a. Eq a => a -> Term c a -> Bool
strictlyPositiveIn = go id
  where
    validArgPi :: forall x. Eq x => (a -> x) -> a -> Term c x -> Bool
    validArgPi ctx val (Pi _ ty rest) =
      ctx val `notElem` ty &&
      validArgPi (F . ctx) val (fromScope rest)
    validArgPi ctx val ty = validArgApp ctx val ty

    validArgApp ctx val (App a b) =
      ctx  val `notElem` b &&
      validArgApp ctx val a
    validArgApp _ _ _ = True

    go :: forall x. Eq x => (a -> x) -> a -> Term c x -> Bool
    go ctx val (Pi _ ty rest) =
      validArgPi ctx val ty &&
      go (F . ctx) val (fromScope rest)
    go _ _ _ = True

checkInductive ::
  (Eq a, Eq c) =>
  (a -> c -> Bool) ->
  (a -> Either a (Entry c a)) ->
  (a -> Either a Usage) ->
  Inductive c a ->
  [InductiveError c a]
checkInductive cmp ctx usages ind = snd $ runWriter go
  where
    go = do
      case checkZero cmp ctx usages (_indTypeType ind) Type of
        Left e -> tell [IndTypeError (_indTypeName ind) e]
        Right _ -> pure ()
      for_ (_indConstructors ind) $ \(n, ty) -> do
        case checkZero cmp ctx usages ty Type of
          Left e -> tell [IndTypeError (_indTypeName ind) e]
          Right _ -> pure ()
        unless (ty `returnsCtor` _indTypeName ind) $
          tell [IndIncorrectType n]
        unless (_indTypeName ind `strictlyPositiveIn` ty) $
          tell [IndNotStrictlyPositive n]