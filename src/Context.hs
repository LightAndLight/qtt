{-# language DeriveFunctor #-}
{-# language ExistentialQuantification #-}
module Context where

import Data.Semiring (times, plus)
import Syntax

data Entry a
  = Entry
  { _entryUsage :: Usage
  , _entryType :: Term a
  } deriving (Eq, Show, Functor)

data Ctx v a
  = Nil
  | Cons v (Entry a) (Ctx v a)
  deriving (Eq, Show)

scaleE :: Usage -> Entry a -> Entry a
scaleE u (Entry u' t) = Entry (times u u') t

zeroE :: Entry a -> Entry a
zeroE = scaleE Zero

scaleCtx :: Usage -> Ctx v a -> Ctx v a
scaleCtx u = go
  where
    go ctx =
      case ctx of
        Nil -> Nil
        Cons v c cs -> Cons v (scaleE u c) (go cs)

zeroCtx :: Ctx v a -> Ctx v a
zeroCtx = scaleCtx Zero

addCtx :: (Eq v, Eq a) => Ctx v a -> Ctx v a -> Ctx v a
addCtx Nil Nil = Nil
addCtx (Cons v (Entry u t) cs) (Cons v' (Entry u' t') cs')
  | v == v' && t == t' = Cons v (Entry (plus u u') t) (addCtx cs cs')
addCtx _ _ =  error "addCtx: Ctx mismatch"

lookupCtx :: Eq v => v -> Ctx v a -> Maybe (Entry a)
lookupCtx _ Nil = Nothing
lookupCtx a (Cons v (Entry u t) cs)
  | v == a = Just $ Entry u t
  | otherwise = lookupCtx a cs

deleteCtx :: Eq v => v -> Ctx v a -> Ctx v a
deleteCtx _ Nil = Nil
deleteCtx a (Cons v e cs)
  | v == a = cs
  | otherwise = Cons v e (deleteCtx a cs)