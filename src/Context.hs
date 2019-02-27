{-# language DeriveFunctor #-}
{-# language TemplateHaskell #-}
module Context where

import Control.Lens.TH (makeLenses)
import Data.Map (Map)

import Syntax

data Entry n l a
  = InductiveEntry { _entryType :: Ty n l a, _entryCtors :: Map n (Term n l a) }
  | BindingEntry { _entryType :: Ty n l a }
  | CtorEntry { _entryType :: Ty n l a }
  deriving (Eq, Show, Functor)
makeLenses ''Entry