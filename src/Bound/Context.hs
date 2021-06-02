{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}

module Bound.Context (
  Context,
  empty,
  fromList,
  lookup,
  insert,
  delete,
  shift,
  merge,
  split,
  zipWithKeyA,
  zipWithKey,
) where

import Bound (Var (..))
import Control.Lens.Indexed (FoldableWithIndex (..))
import Data.Foldable (foldl')
import Data.Functor.Identity (Identity (..))
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Map.Merge.Strict as Map.Merge
import Data.These (These (..))
import Prelude hiding (lookup)

data Context k v where
  Free :: Map k v -> Context k v
  Binder :: (Ord k, Ord k') => Map k v -> Context k' v -> Context (Var k k') v

deriving instance Functor (Context k)
deriving instance Foldable (Context k)
deriving instance Traversable (Context k)

instance FoldableWithIndex k (Context k) where
  ifoldMap f ctx =
    case ctx of
      Free frees -> ifoldMap f frees
      Binder bs ctx' -> ifoldMap (f . B) bs <> ifoldMap (f . F) ctx'

instance Ord k => Semigroup (Context k v) where
  ctx1 <> ctx2 =
    case ctx1 of
      Free frees1 ->
        Map.foldlWithKey (\acc k v -> insert k v acc) ctx2 frees1
      Binder bs1 ctx1' ->
        let (bs2, ctx2') = split ctx2
         in Binder (bs1 <> bs2) (ctx1' <> ctx2')

instance Ord k => Monoid (Context k v) where
  mempty = empty

empty :: Ord k => Context k v
empty = Free mempty

fromList :: Ord k => [(k, v)] -> Context k v
fromList = foldl' (\acc (k, v) -> insert k v acc) empty

lookup :: Ord k => k -> Context k v -> Maybe v
lookup k ctx =
  case ctx of
    Free frees -> Map.lookup k frees
    Binder bs ctx' ->
      case k of
        B k' -> Map.lookup k' bs
        F k' -> lookup k' ctx'

insert :: Ord k => k -> v -> Context k v -> Context k v
insert k v ctx =
  case ctx of
    Free frees -> Free (Map.insert k v frees)
    Binder bs ctx' ->
      case k of
        B k' -> Binder (Map.insert k' v bs) ctx'
        F k' -> Binder bs (insert k' v ctx')

delete :: Ord k => k -> Context k v -> Context k v
delete k ctx =
  case ctx of
    Free frees -> Free (Map.delete k frees)
    Binder bs ctx' ->
      case k of
        B k' -> Binder (Map.delete k' bs) ctx'
        F k' -> Binder bs (delete k' ctx')

shift :: (Ord a, Ord b) => Context b v -> Context (Var a b) v
shift = Binder mempty

merge :: (Ord a, Ord b) => Map a v -> Context b v -> Context (Var a b) v
merge a b =
  Map.foldlWithKey
    (\acc k v -> insert (B k) v acc)
    (shift b)
    a

split :: (Ord a, Ord b) => Context (Var a b) v -> (Map a v, Context b v)
split ctx =
  case ctx of
    Free frees ->
      Map.foldlWithKey'
        ( \(mav, cbc) k v ->
            case k of
              B k' -> (Map.insert k' v mav, cbc)
              F k' -> (mav, insert k' v cbc)
        )
        (mempty, empty)
        frees
    Binder bs ctx' -> (bs, ctx')

zipWithKeyA ::
  (Ord k, Applicative m) =>
  (k -> These a b -> m (Maybe c)) ->
  Context k a ->
  Context k b ->
  m (Context k c)
zipWithKeyA f ctx1 ctx2 =
  case ctx1 of
    Free frees1 ->
      case ctx2 of
        Free frees2 ->
          Free <$> ezpz f frees1 frees2
        Binder bs2 ctx2' ->
          let (bs1, ctx1') = split ctx1
           in Binder <$> ezpz (f . B) bs1 bs2 <*> zipWithKeyA (f . F) ctx1' ctx2'
    Binder bs1 ctx1' ->
      case ctx2 of
        Free{} ->
          let (bs2, ctx2') = split ctx2
           in Binder <$> ezpz (f . B) bs1 bs2 <*> zipWithKeyA (f . F) ctx1' ctx2'
        Binder bs2 ctx2' ->
          Binder <$> ezpz (f . B) bs1 bs2 <*> zipWithKeyA (f . F) ctx1' ctx2'
 where
  ezpz ::
    (Ord k, Applicative m) =>
    (k -> These a b -> m (Maybe c)) ->
    Map k a ->
    Map k b ->
    m (Map k c)
  ezpz g =
    Map.Merge.mergeA
      (Map.Merge.traverseMaybeMissing $ \k a -> g k (This a))
      (Map.Merge.traverseMaybeMissing $ \k b -> g k (That b))
      (Map.Merge.zipWithMaybeAMatched $ \k a b -> g k (These a b))

zipWithKey ::
  Ord k =>
  (k -> These a b -> Maybe c) ->
  Context k a ->
  Context k b ->
  Context k c
zipWithKey f a b = runIdentity $ zipWithKeyA (\k -> Identity . f k) a b