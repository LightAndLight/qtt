{-# language EmptyCase #-}
{-# language GADTs #-}
{-# language LambdaCase #-}
module Syntax.Pretty where

import Bound.Scope (fromScope)
import Bound.Var (unvar)
import Control.Lens.Cons (_Snoc)
import Control.Lens.Fold ((^?))
import Data.Bool (bool)
import Data.List.NonEmpty (NonEmpty(..))
import Text.PrettyPrint.ANSI.Leijen (Pretty(..), Doc)

import qualified Text.PrettyPrint.ANSI.Leijen as Pretty

import Syntax

hangCase :: (Term c a -> Doc) -> Term c a -> Doc
hangCase f a@Case{} = Pretty.line <> Pretty.indent 2 (f a)
hangCase f a = f a

prettyBranch :: Pretty c => [Int] -> (a -> Doc) -> Branch c (Term c) a -> Doc
prettyBranch supply pvar (Branch a b) =
  case a of
    PVar ->
      case supply of
        [] -> undefined
        n : supply' ->
          let
            vname = Pretty.char 'x' <> Pretty.int n
          in
            Pretty.hsep
            [ vname
            , Pretty.text "=>"
            , hangCase
                (prettyTerm' supply' (unvar (\case; V -> vname) pvar))
                (fromScope b)
            ]
    PCtor s n ->
      let
        (ns, supply') = splitAt n supply
        vnames = (Pretty.char 'x' <>) . Pretty.int <$> ns
      in
        Pretty.hsep $
        pretty s :
        vnames <>
        [ Pretty.text "=>"
        , hangCase
            (prettyTerm' supply' (unvar (\case; C i -> vnames !! i) pvar))
            (fromScope b)
        ]
    PWild ->
      Pretty.hsep
      [ Pretty.text "_ =>"
      , hangCase (prettyTerm' supply (unvar (\case {}) pvar)) (fromScope b)
      ]

prettyTerm :: (Pretty c, Pretty a) => Term c a -> Doc
prettyTerm = prettyTerm' [0..] pretty

prettyTerm' :: Pretty c => [Int] -> (a -> Doc) -> Term c a -> Doc
prettyTerm' supply pvar tm =
  case tm of
    Var a -> pvar a
    Ann a b c ->
      Pretty.hsep
      [ (case a of
            Lam{} -> Pretty.parens
            Pi{} -> Pretty.parens
            Case{} -> Pretty.parens
            UnpackTensor{} -> Pretty.parens
            _ -> id)
        (prettyTerm' supply pvar a)
      , Pretty.char ':' <> pretty b
      , prettyTerm' supply pvar c
      ]
    Type -> Pretty.text "Type"
    Lam s ->
      case supply of
        [] -> undefined
        n : supply' ->
          let
            varname = Pretty.char 'x' <> Pretty.int n
          in
            Pretty.hsep
            [ Pretty.char '\\' <> varname
            , Pretty.text "=>"
            , hangCase
                (prettyTerm' supply' (unvar (const varname) pvar))
                (fromScope s)
            ]
    Pi a b c ->
      case supply of
        [] -> undefined
        n : supply' ->
          let
            varname = Pretty.char 'x' <> Pretty.int n
          in
            Pretty.hsep
            [ Pretty.parens $
              Pretty.hsep
              [ varname
              , Pretty.char ':' <> pretty a
              , prettyTerm' supply' pvar b
              ]
            , Pretty.text "->"
            , prettyTerm' supply' (unvar (const varname) pvar) (fromScope c)
            ]
    App a b ->
      Pretty.hsep
      [ (case a of
            Lam{} -> Pretty.parens
            Pi{} -> Pretty.parens
            UnpackTensor{} -> Pretty.parens
            Case{} -> Pretty.parens
            _ -> id)
        (prettyTerm' supply pvar a)
      , (case b of
            Lam{} -> Pretty.parens
            Pi{} -> Pretty.parens
            UnpackTensor{} -> Pretty.parens
            App{} -> Pretty.parens
            Fst{} -> Pretty.parens
            Snd{} -> Pretty.parens
            Case{} -> Pretty.parens
            _ -> id)
        (prettyTerm' supply pvar b)
      ]
    MkTensor a b ->
      Pretty.parens $
      prettyTerm' supply pvar a <>
      Pretty.comma <> Pretty.space <>
      prettyTerm' supply pvar b
    Tensor a b ->
      case supply of
        [] -> undefined
        n:supply' ->
          let
            varname = Pretty.char 'x' <> Pretty.int n
          in
            Pretty.parens $
            Pretty.hsep [varname, Pretty.char ':', prettyTerm' supply' pvar a] <>
            Pretty.char '⨂' <> Pretty.space <>
            prettyTerm' supply' (unvar (const varname) pvar) (fromScope b)
    UnpackTensor a b ->
      case supply of
        [] -> undefined
        [_] -> undefined
        m:n:supply' ->
          let
            v1 = Pretty.char 'x' <> Pretty.int m
            v2 = Pretty.char 'x' <> Pretty.int n
          in
            Pretty.hsep
            [ Pretty.text "let"
            , Pretty.parens $ v1 <> Pretty.comma <> Pretty.space <> v2
            , Pretty.char '='
            , (case a of
                  UnpackTensor{} -> Pretty.parens
                  _ -> id)
              (prettyTerm' supply' pvar a)
            , Pretty.text "in"
            , prettyTerm' supply' (unvar (bool v1 v2) pvar) (fromScope b)
            ]
    MkWith a b ->
      Pretty.parens $
      prettyTerm' supply pvar a <>
      Pretty.comma <> Pretty.space <>
      prettyTerm' supply pvar b
    With a b ->
      case supply of
        [] -> undefined
        n:supply' ->
          let
            varname = Pretty.char 'x' <> Pretty.int n
          in
            Pretty.parens $
            Pretty.hsep [varname, Pretty.char ':', prettyTerm' supply' pvar a] <>
            Pretty.char '&' <> Pretty.space <>
            prettyTerm' supply' (unvar (const varname) pvar) (fromScope b)
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
        (prettyTerm' supply pvar a)
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
        (prettyTerm' supply pvar a)
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
        (prettyTerm' supply pvar a)
      , Pretty.text "of"
      ] Pretty.<$>
      Pretty.indent 2
      (Pretty.char '{' <> Pretty.space <> prettyBranch supply pvar bh Pretty.<$>
        case brest ^? _Snoc of
          Nothing -> Pretty.char '}'
          Just (bmiddle, blast) ->
            foldMap
              ((\x -> Pretty.char ';' <> Pretty.space <> x <> Pretty.line) .
              prettyBranch supply pvar)
              bmiddle <>
            Pretty.char ';' <> Pretty.space <> prettyBranch supply pvar blast Pretty.<$>
            Pretty.char '}')