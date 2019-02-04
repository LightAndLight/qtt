module Typecheck where

import Bound.Scope (fromScope)
import Bound.Var (Var(..), unvar)

import Context
import Syntax

data TypeError a
  = NotInScope a
  | VariableMany a
  | ExpectedType (Ty a)
  deriving (Eq, Show)

eval :: Context a -> Term a -> Term a
eval ctx tm =
  case tm of
    Var a -> _
    Ann a u b -> _
    Type -> Type
    Lam a -> _
    Pi u a b -> _
    App a b -> _
    Pair a b -> _
    Sigma u a b -> _
    Fst a -> _
    Snd a -> _

check :: Context a -> (x -> Entry () x) -> Term x -> Usage -> Ty x -> Either (TypeError a) Bool
check ctx varCtx tm u ty =
  case tm of
    Pi u a b ->
      case ty of
        Type -> do
          check (zeroC ctx) varCtx a Zero Type
          check (zeroC ctx) (unvar (const $ Entry () Zero (F <$> a)) (fmap F . varCtx)) (fromScope b) Zero Type
        _ -> Left $ ExpectedType ty

infer :: Eq a => Context a -> Term a -> Either (TypeError a) (Usage, Ty a)
infer ctx tm =
  case tm of
    Var a ->
      case lookupC a ctx of
        Nothing -> Left $ NotInScope a
        Just (Entry _ u t) ->
          case u of
            Many -> Left $ VariableMany a
            _ -> pure (u, t)
    Ann a u b -> do
      check (zeroC ctx) b Zero Type
      check (zeroC ctx) a Zero b
      pure (u, b)