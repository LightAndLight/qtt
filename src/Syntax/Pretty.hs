module Syntax.Pretty where

import Bound.Scope (fromScope)
import Bound.Var (unvar)
import Data.Bool (bool)
import Text.PrettyPrint.ANSI.Leijen (Pretty(..), Doc)

import qualified Text.PrettyPrint.ANSI.Leijen as Pretty

import Syntax

prettyTerm :: (a -> Doc) -> Term a -> Doc
prettyTerm = go [0..]
  where
    go :: [Int] -> (a -> Doc) -> Term a -> Doc
    go supply pvar tm =
      case tm of
        Var a -> pvar a
        Ann a b c ->
          Pretty.hsep
          [ (case a of
               Lam{} -> Pretty.parens
               Pi{} -> Pretty.parens
               UnpackSigma{} -> Pretty.parens
               _ -> id)
            (go supply pvar a)
          , Pretty.char ':' <> pretty b
          , go supply pvar c
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
                , go supply' (unvar (const varname) pvar) (fromScope s)
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
                  , go supply' pvar b
                  ]
                , Pretty.text "->"
                , go supply' (unvar (const varname) pvar) (fromScope c)
                ]
        App a b ->
          Pretty.hsep
          [ (case a of
               Lam{} -> Pretty.parens
               Pi{} -> Pretty.parens
               UnpackSigma{} -> Pretty.parens
               _ -> id)
            (go supply pvar a)
          , (case b of
               Lam{} -> Pretty.parens
               Pi{} -> Pretty.parens
               UnpackSigma{} -> Pretty.parens
               App{} -> Pretty.parens
               Fst{} -> Pretty.parens
               Snd{} -> Pretty.parens
               _ -> id)
            (go supply pvar b)
          ]
        Pair a b ->
          Pretty.parens $
          go supply pvar a <>
          Pretty.comma <> Pretty.space <>
          go supply pvar b
        Sigma a b c ->
          case supply of
            [] -> undefined
            n:supply' ->
              let
                varname = Pretty.char 'x' <> Pretty.int n
              in
                Pretty.parens $
                Pretty.hsep [varname, Pretty.char ':' <> pretty a, go supply' pvar b] <>
                Pretty.comma <> Pretty.space <>
                go supply' (unvar (const varname) pvar) (fromScope c)
        UnpackSigma a b ->
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
                     UnpackSigma{} -> Pretty.parens
                     _ -> id)
                  (go supply' pvar a)
                , Pretty.text "in"
                , go supply' (unvar (bool v1 v2) pvar) (fromScope b)
                ]
        Fst a ->
          Pretty.hsep
          [ Pretty.text "fst"
          , (case a of
               App{} -> Pretty.parens
               Fst{} -> Pretty.parens
               Snd{} -> Pretty.parens
               _ -> id)
            (go supply pvar a)
          ]
        Snd a ->
          Pretty.hsep
          [ Pretty.text "snd"
          , (case a of
               App{} -> Pretty.parens
               Fst{} -> Pretty.parens
               Snd{} -> Pretty.parens
               _ -> id)
            (go supply pvar a)
          ]
        Unit -> Pretty.text "Unit"
        MkUnit -> Pretty.text "unit"