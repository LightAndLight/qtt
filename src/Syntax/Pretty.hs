{-# language EmptyCase #-}
{-# language GADTs #-}
{-# language LambdaCase #-}
module Syntax.Pretty where

import Bound.Scope (fromScope)
import Bound.Var (unvar)
import Control.Lens.Cons (_Snoc)
import Control.Lens.Fold ((^?))
import Data.List.NonEmpty (NonEmpty(..))
import Text.PrettyPrint.ANSI.Leijen (Pretty(..), Doc)

import qualified Bound.Name as Bound
import qualified Text.PrettyPrint.ANSI.Leijen as Pretty

import Syntax

hangCase :: (Term n l a -> Doc) -> Term n l a -> Doc
hangCase f a@Case{} = Pretty.line <> Pretty.indent 2 (f a)
hangCase f a = f a

prettyPattern :: Pretty n => Pattern n a -> Doc
prettyPattern p =
  case p of
    PVar n -> pretty n
    PCtor s ns _ -> Pretty.hsep $ pretty s : fmap pretty ns

prettyBranch :: Pretty n => (a -> Doc) -> Branch n (Term n l) a -> Doc
prettyBranch _ (BranchImpossible a) =
  Pretty.hsep $
  [ prettyPattern a
  , Pretty.text "impossible"
  ]
prettyBranch pvar (Branch a b) =
  Pretty.hsep $
  [ prettyPattern a
  , Pretty.text "=>"
  , hangCase
      (prettyTerm (unvar (pretty . Bound.name) pvar))
      (fromScope b)
  ]

prettyTerm :: Pretty n => (a -> Doc) -> Term n l a -> Doc
prettyTerm pvar tm =
  case tm of
    Loc _ a -> prettyTerm pvar a
    Var a -> pvar a
    Ann a b c ->
      Pretty.hsep
      [ (case a of
            Lam{} -> Pretty.parens
            Pi{} -> Pretty.parens
            UnpackTensor{} -> Pretty.parens
            Case{} -> Pretty.parens
            _ -> id)
        (prettyTerm pvar a)
      , Pretty.char ':' <> pretty b
      , prettyTerm pvar c
      ]
    Type -> Pretty.text "Type"
    Lam n s ->
      Pretty.hsep
      [ Pretty.char '\\' <> pretty n
      , Pretty.text "=>"
      , prettyTerm (unvar (pretty . Bound.name) pvar) (fromScope s)
      ]
    Pi a mn b c ->
      Pretty.hsep
      [ Pretty.parens $
        Pretty.hsep
        [ maybe (Pretty.char '_') pretty mn
        , Pretty.char ':' <> pretty a
        , prettyTerm pvar b
        ]
      , Pretty.text "->"
      , prettyTerm (unvar (pretty . Bound.name) pvar) (fromScope c)
      ]
    App a b ->
      Pretty.hsep
      [ (case a of
            Lam{} -> Pretty.parens
            Pi{} -> Pretty.parens
            UnpackTensor{} -> Pretty.parens
            Case{} -> Pretty.parens
            _ -> id)
        (prettyTerm pvar a)
      , (case b of
            Lam{} -> Pretty.parens
            Pi{} -> Pretty.parens
            UnpackTensor{} -> Pretty.parens
            App{} -> Pretty.parens
            Fst{} -> Pretty.parens
            Snd{} -> Pretty.parens
            Case{} -> Pretty.parens
            _ -> id)
        (prettyTerm pvar b)
      ]
    MkTensor a b ->
      Pretty.parens $
      prettyTerm pvar a <>
      Pretty.comma <> Pretty.space <>
      prettyTerm pvar b
    Tensor n a b ->
      Pretty.parens $
      Pretty.hsep [pretty n, Pretty.char ':', prettyTerm pvar a] <>
      Pretty.char '⨂' <> Pretty.space <>
      prettyTerm (unvar (pretty . Bound.name) pvar) (fromScope b)
    UnpackTensor n1 n2 a b ->
      Pretty.hsep
      [ Pretty.text "let"
      , Pretty.parens $
        pretty n1 <> Pretty.comma <> Pretty.space <> pretty n2
      , Pretty.char '='
      , (case a of
            UnpackTensor{} -> Pretty.parens
            _ -> id)
        (prettyTerm pvar a)
      , Pretty.text "in"
      , prettyTerm (unvar (pretty . Bound.name) pvar) (fromScope b)
      ]
    MkWith a b ->
      Pretty.parens $
      prettyTerm pvar a <>
      Pretty.comma <> Pretty.space <>
      prettyTerm pvar b
    With n a b ->
      Pretty.parens $
      Pretty.hsep [pretty n, Pretty.char ':', prettyTerm pvar a] <>
      Pretty.char '&' <> Pretty.space <>
      prettyTerm (unvar (pretty . Bound.name) pvar) (fromScope b)
    Fst a ->
      Pretty.hsep
      [ Pretty.text "fst"
      , (case a of
            App{} -> Pretty.parens
            Pi{} -> Pretty.parens
            Lam{} -> Pretty.parens
            Case{} -> Pretty.parens
            Fst{} -> Pretty.parens
            Snd{} -> Pretty.parens
            _ -> id)
        (prettyTerm pvar a)
      ]
    Snd a ->
      Pretty.hsep
      [ Pretty.text "snd"
      , (case a of
            App{} -> Pretty.parens
            Pi{} -> Pretty.parens
            Lam{} -> Pretty.parens
            Case{} -> Pretty.parens
            Fst{} -> Pretty.parens
            Snd{} -> Pretty.parens
            _ -> id)
        (prettyTerm pvar a)
      ]
    Unit -> Pretty.text "Unit"
    MkUnit -> Pretty.text "unit"
    Case a (bh :| brest) ->
      Pretty.hsep
      [ Pretty.text "case"
      , (case a of
           Case{} -> Pretty.parens
           Lam{} -> Pretty.parens
           Pi{} -> Pretty.parens
           _ -> id)
        (prettyTerm pvar a)
      , Pretty.text "of"
      ] Pretty.<$>
      Pretty.indent 2
      (Pretty.char '{' <> Pretty.space <> prettyBranch pvar bh Pretty.<$>
        case brest ^? _Snoc of
          Nothing -> Pretty.char '}'
          Just (bmiddle, blast) ->
            foldMap
              ((\x -> Pretty.char ';' <> Pretty.space <> x <> Pretty.line) .
              prettyBranch pvar)
              bmiddle <>
            Pretty.char ';' <> Pretty.space <> prettyBranch pvar blast Pretty.<$>
            Pretty.char '}')
