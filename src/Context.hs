{-# language DeriveFunctor #-}
module Context where

import Data.Semiring (times, plus)
import Syntax

data Entry v a
  = Entry
  { _entryVar :: v
  , _entryUsage :: Usage
  , _entryType :: Term a
  } deriving (Eq, Show, Functor)

newtype Context a = Context { unContext :: [Entry a a] }
  deriving (Eq, Show)

scaleC :: Usage -> Context a -> Context a
scaleC u = Context . go . unContext
  where
    go ctx =
      case ctx of
        [] -> []
        Entry v u' t : cs -> Entry v (times u u') t : go cs

zeroC :: Context a -> Context a
zeroC = scaleC Zero

addC :: Eq a => Context a -> Context a -> Context a
addC (Context a) (Context b) = Context $ go a b
  where
    go [] [] = []
    go (Entry v u t : cs) (Entry v' u' t' : cs')
      | v == v' && t == t' = Entry v (plus u u') t : go cs cs'
    go _ _ =  error "addContext: context mismatch"

lookupC :: Eq a => a -> Context a -> Maybe (Entry a a)
lookupC a = go . unContext
  where
    go [] = Nothing
    go (Entry v u t : cs)
      | v == a = Just $ Entry v u t
      | otherwise = go cs