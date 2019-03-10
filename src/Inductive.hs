{-# language FlexibleContexts #-}
{-# language ScopedTypeVariables #-}
module Inductive where

import Bound.Scope (fromScope)
import Bound.Var (Var(..))
import Control.Monad (unless)
import Control.Monad.Writer.Strict (runWriter, tell)
import Data.Map (Map)
import Data.String (IsString)

import qualified Data.Map as Map

import Context
import Syntax
import TypeError
import Typecheck

data Inductive n l a
  = Inductive
  { _indTypeName :: a
  , _indTypeType :: Term n l a
  , _indConstructors :: Map a (Term n l a)
  } deriving (Eq, Show)

data InductiveError l a
  = IndTypeError a (TypeError l a)
  | IndIncorrectType a
  | IndNotStrictlyPositive a
  deriving (Eq, Show)

returnsCtor :: forall n l a. Eq a => Term n l a -> a -> Bool
returnsCtor = go id
  where
    go :: forall x. Eq x => (a -> x) -> Term n l x -> a -> Bool
    go ctx (App (App (Pi _) _) (Lam _ rest)) val = go (F . ctx) (fromScope rest) val
    go ctx (App a _) val = go ctx a val
    go ctx (Var a) val = a == ctx val
    go _ _ _ = False

strictlyPositiveIn :: forall n l a. Eq a => a -> Term n l a -> Bool
strictlyPositiveIn = go id
  where
    validArgPi :: forall x. Eq x => (a -> x) -> a -> Term n l x -> Bool
    validArgPi ctx val (App (App (Pi _) ty) (Lam _ rest)) =
      ctx val `notElem` ty &&
      validArgPi (F . ctx) val (fromScope rest)
    validArgPi ctx val ty = validArgApp ctx val ty

    validArgApp ctx val (App a b) =
      ctx  val `notElem` b &&
      validArgApp ctx val a
    validArgApp _ _ _ = True

    go :: forall x. Eq x => (a -> x) -> a -> Term n l x -> Bool
    go ctx val (App (App (Pi _) ty) (Lam _ rest)) =
      validArgPi ctx val ty &&
      go (F . ctx) val (fromScope rest)
    go _ _ _ = True

checkInductive ::
  (Ord a, IsString a, Monoid a) =>
  (a -> Maybe (Entry a l a)) ->
  (a -> Maybe Usage) ->
  Inductive a l a ->
  [InductiveError l a]
checkInductive ctx usages ind = snd $ runWriter go
  where
    go = do
      case checkZero (Env id id ctx usages) (_indTypeType ind) Type of
        Left e -> tell [IndTypeError (_indTypeName ind) e]
        Right _ -> pure ()
      Map.traverseWithKey checkCtor (_indConstructors ind)

    checkCtor n ty = do 
      case checkZero (Env id id ctx usages) ty Type of
        Left e -> tell [IndTypeError (_indTypeName ind) e]
        Right _ -> pure ()
      unless (ty `returnsCtor` _indTypeName ind) $
        tell [IndIncorrectType n]
      unless (_indTypeName ind `strictlyPositiveIn` ty) $
        tell [IndNotStrictlyPositive n]