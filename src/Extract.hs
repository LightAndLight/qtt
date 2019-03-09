{-# language OverloadedStrings #-}
{-# language ScopedTypeVariables #-}
module Extract where

import Bound.Name (instantiate1Name)
import Bound.Scope (Scope, fromScope)
import Bound.Var (Var(..), unvar)
import Control.Applicative (empty)
import Control.Comonad (extract)
import Control.Lens.Fold ((^?))
import Control.Lens.Getter (view)
import Control.Lens.Prism (_Right)
import Control.Lens.Tuple (_3)
import Data.Bool (bool)
import Data.List (intersperse)
import Data.Semiring (times)
import Data.String (IsString)
import Data.Text (Text)
import Text.PrettyPrint.ANSI.Leijen (Pretty(..), Doc)

import qualified Bound.Name as Name
import qualified Data.Text as Text
import qualified Text.PrettyPrint.ANSI.Leijen as Pretty

import Context
import Syntax
import Typecheck

data HsPat a
  = HsPatCtor Text [HsPat a]
  | HsPatVar a
  | HsPatProxy
  | HsPatAnn (HsPat a) (HsTy a)
  | HsPatWild
data HsTm a
  = HsTmUnit
  | HsTmFst
  | HsTmSnd
  | HsTmPair (HsTm a) (HsTm a)
  | HsTmApp (HsTm a) (HsTm a)
  | HsTmLet (HsPat a) (HsTm a) (HsTm a)
  | HsTmVar a
  | HsTmLam (HsPat a) (HsTm a)
  | HsTmProxy
  | HsTmCase (HsTm a) [(HsPat a, HsTm a)]
  | HsTmAnn (HsTm a) (HsTy a)
data HsTy a
  = HsTyUnit
  | HsTyProxy
  | HsTyVar a
  | HsTyApp (HsTy a) (HsTy a)
  | HsTyForall a (HsTy a)
  | HsTyCtor Text
  | HsArr (HsTy a) (HsTy a)
data HsDef a
  = HsDefData Text [a] [([a], Text, [HsTy a])]
  | HsDefGADT Text [a] [(Text, [HsTy a], HsTy a)]
  | HsDefValue a (HsTm a)

instance Pretty a => Pretty (HsPat a) where
  pretty pat =
    case pat of
      HsPatWild -> Pretty.char '_'
      HsPatVar a -> pretty a
      HsPatCtor a b ->
        Pretty.hsep $
        Pretty.text (Text.unpack a) :
        fmap
          (\x ->
             (case x of
                HsPatCtor{} -> Pretty.parens
                HsPatAnn{} -> Pretty.parens
                _ -> id)
             (pretty x))
          b
      HsPatAnn a b -> Pretty.hsep [pretty a, Pretty.text "::", pretty b]
      HsPatProxy -> Pretty.text "proxy#"

instance Pretty a => Pretty (HsTm a) where
  pretty tm =
    case tm of
      HsTmUnit -> Pretty.text "()"
      HsTmFst -> Pretty.text "fst"
      HsTmSnd -> Pretty.text "snd"
      HsTmPair a b ->
        Pretty.parens $
        pretty a <> Pretty.comma <> Pretty.space <> pretty b
      HsTmApp a b ->
        Pretty.hsep
        [ (case a of
             HsTmLet{} -> Pretty.parens
             HsTmLam{} -> Pretty.parens
             HsTmAnn{} -> Pretty.parens
             _ -> id)
          (pretty a)
        , (case b of
             HsTmApp{} -> Pretty.parens
             HsTmLet{} -> Pretty.parens
             HsTmLam{} -> Pretty.parens
             HsTmAnn{} -> Pretty.parens
             _ -> id)
          (pretty b)
        ]
      HsTmLet a b c ->
        Pretty.hsep
        [ Pretty.text "let"
        , pretty a
        , Pretty.char '='
        , (case b of
             HsTmLet{} -> Pretty.parens
             _ -> id)
          (pretty b)
        , Pretty.text "in"
        ] Pretty.<$>
        pretty c
      HsTmVar a -> pretty a
      HsTmLam a b ->
        Pretty.char '\\' <>
        Pretty.hsep
        [ (case a of
             HsPatCtor{} -> Pretty.parens
             HsPatAnn{} -> Pretty.parens
             _ -> id)
          (pretty a)
        , Pretty.text "->"
        , pretty b
        ]
      HsTmProxy -> Pretty.text "proxy#"
      HsTmCase a b ->
        Pretty.hsep
        [ Pretty.text "case"
        , pretty a
        , Pretty.text "of"
        ] Pretty.<$>
        Pretty.indent 2
        (Pretty.vsep $
         fmap
           (\(x, y) ->
              Pretty.hsep [pretty x, Pretty.text "->", pretty y])
           b)
      HsTmAnn a b ->
        Pretty.hsep
        [ (case a of
             HsTmLam{} -> Pretty.parens
             HsTmCase{} -> Pretty.parens
             HsTmLet{} -> Pretty.parens
             _ -> id)
          (pretty a)
        , Pretty.text "::"
        , pretty b
        ]

instance Pretty a => Pretty (HsTy a) where
  pretty ty =
    case ty of
      HsArr a b ->
        Pretty.hsep
        [ (case a of
             HsArr{} -> Pretty.parens
             _ -> id)
          (pretty a)
        , Pretty.text "->"
        , pretty b
        ]
      HsTyUnit -> Pretty.text "()"
      HsTyProxy -> Pretty.text "Proxy#"
      HsTyVar a -> pretty a
      HsTyApp a b ->
        Pretty.hsep
        [ (case a of
             HsTyForall{} -> Pretty.parens
             _ -> id)
          (pretty a)
        , (case b of
             HsTyApp{} -> Pretty.parens
             HsTyForall{} -> Pretty.parens
             _ -> id)
          (pretty b)
        ]
      HsTyForall a b ->
        Pretty.hsep
        [ Pretty.text "forall"
        , pretty a <> Pretty.dot
        , pretty b
        ]
      HsTyCtor a -> Pretty.text $ Text.unpack a

instance Pretty a => Pretty (HsDef a) where
  pretty def =
    case def of
      HsDefData a b c ->
        Pretty.hsep ([Pretty.text "data", Pretty.text $ Text.unpack a] <> fmap pretty b) <>
        (if null c then mempty else Pretty.space <> Pretty.char '=') Pretty.<$>
        Pretty.indent 2 (Pretty.vsep $ prettyBranches c)
        where
          prettyBranch :: ([a], Text, [HsTy a]) -> Doc
          prettyBranch (exs, ctor, args) =
            (if null exs
             then mempty
             else
               Pretty.hsep ([Pretty.text "forall"] <> fmap pretty exs) <>
               Pretty.char '.' <>
               Pretty.space) <>
            pretty (foldl HsTyApp (HsTyCtor ctor) args)

          prettyBranches :: [([a], Text, [HsTy a])] -> [Doc]
          prettyBranches [] = []
          prettyBranches [br] = [prettyBranch br]
          prettyBranches (br : rest) =
            Pretty.hsep [prettyBranch br, Pretty.char '|'] :
            prettyBranches rest
      HsDefValue a b ->
        Pretty.hsep [pretty a, Pretty.char '='] Pretty.<$>
        Pretty.indent 2 (pretty b)
      HsDefGADT a b c ->
        Pretty.hsep
          (Pretty.text "data" :
           Pretty.text (Text.unpack a) :
           fmap pretty b <>
           [Pretty.text "where"]) Pretty.<$>
        Pretty.indent 2
        (Pretty.vsep $
         fmap
           (\(d, e, f) ->
              Pretty.hsep $
              Pretty.text (Text.unpack d) :
              Pretty.text "::" :
              intersperse (Pretty.text "->") (fmap pretty e) <>
              [Pretty.text "->", pretty f])
           c)

prelude :: IsString a => [HsDef a]
prelude =
  [ HsDefGADT "TensorE" ["f"]
    [ ( "TensorE"
      , [HsTyApp HsTyProxy (HsTyVar "a"), HsTyApp (HsTyVar "f") (HsTyVar "a")]
      , HsTyApp (HsTyCtor "TensorE") (HsTyVar "f")
      )
    ]
  , HsDefGADT "TensorP" ["a", "b"]
    [ ( "TensorP"
      , [HsTyVar "a", HsTyVar "b"]
      , HsTyApp (HsTyApp (HsTyCtor "TensorP") (HsTyVar "a")) (HsTyVar "b")
      )
    ]
  , HsDefData "WithE" ["f"]
    [(["a"], "WithE", [HsTyApp HsTyProxy (HsTyVar "a"), HsTyApp (HsTyVar "f") (HsTyVar "a")])]
  , HsDefData "WithP" ["a", "b"]
    [([], "WithP", [HsTyVar "a", HsTyVar "b"])]
  , HsDefValue "fst" $
    HsTmLam (HsPatCtor "WithP" [HsPatVar "a", HsPatWild]) (HsTmVar "a")
  , HsDefValue "snd" $
    HsTmLam (HsPatCtor "WithP" [HsPatWild, HsPatVar "b"]) (HsTmVar "b")
  ]

extractType :: forall a l x. (x -> HsTy a) -> Term a l x -> Maybe (HsTy a)
extractType depth ty =
  case ty of
    Var a -> pure $ depth a
    Ann a _ _ -> extractType depth a
    Type -> empty

    Lam{} -> empty
    Pi _ a b c ->
      HsArr (HsTyApp HsTyProxy $ maybe HsTyUnit HsTyVar a) <$>
      case b of
        Type -> extractType (unvar (HsTyVar . Name.name) depth) (fromScope c)
        _ -> extractType (unvar (const $ HsTyUnit) depth) (fromScope c)
    App a b -> HsTyApp <$> extractType depth a <*> extractType depth b

    MkTensor{} -> empty
    Tensor _ a b -> genProduct "Tensor" a b
    UnpackTensor{} -> empty

    MkWith{} -> empty
    With _ a b -> genProduct "With" a b
    Fst{} -> empty
    Snd{} -> empty

    Unit -> pure HsTyUnit
    MkUnit -> empty

    Case{} -> empty

    Loc _ a -> extractType depth a
  where
    genProduct :: Text -> Term a l x -> Scope (Name.Name a ()) (Term a l) x -> Maybe (HsTy a)
    genProduct name a b =
      case a of
        Type ->
          case traverse (unvar (Left . HsTyVar . Name.name) Right) (fromScope b) of
            Left x -> pure $ HsTyApp (HsTyCtor $ name <> "E") x
            Right x ->
              HsTyApp <$>
              (HsTyApp (HsTyCtor $ name <> "P") <$> extractType depth a) <*>
              extractType depth x
        _ ->
          HsTyApp <$>
          (HsTyApp (HsTyCtor $ name <> "P") <$> extractType depth a) <*>
          extractType (unvar (const $ HsTyUnit) depth) (fromScope b)

isType :: Term n l a -> Bool
isType ty =
  case ty of
    Var _ -> False
    Ann a _ _ -> isType a
    Type -> True

    Lam{} -> False
    Pi _ _ a b -> isType a && isType (fromScope b)
    App a b -> isType a && isType b

    MkTensor{} -> False
    Tensor _ a b -> isType a && isType (fromScope b)
    UnpackTensor{} -> False

    MkWith{} -> False
    With _ a b -> isType a && isType (fromScope b)
    Fst{} -> False
    Snd{} -> False

    Unit -> True
    MkUnit -> False

    Case{} -> False

    Loc _ a -> isType a

extractTerm ::
  (Ord x, Ord a) =>
  (x -> HsTy a) ->
  Env a l x ->
  Term a l x ->
  Usage ->
  Ty a l x ->
  Maybe (HsTm a)
extractTerm tyctx env tm u ty =
  case tm of
    Var a -> do
      usage <- view envUsages env a
      pure $
        case usage of
          Zero -> HsTmProxy
          _ -> HsTmVar $ view envNames env a
    Ann a u' b -> extractTerm tyctx env a u' b
    Type -> Nothing

    Lam n a ->
      case ty of
        Pi u' _ s t ->
          HsTmLam
          (case u' of
             Zero -> HsPatWild
             _ -> HsPatVar n) <$>
          extractTerm
            (unvar (const HsTyUnit) tyctx)
            (deeperEnv
               Name.name
               (const $ Just $ BindingEntry s)
               (const $ Just $ times u' u)
               env)
            (fromScope a)
            u
            (fromScope t)
        _ -> Nothing
    Pi{} -> Nothing
    App a b -> do
      aty <- infer env a u ^? _Right._3
      case aty of
        Pi u' _ s _ ->
          HsTmApp <$>
            extractTerm tyctx env a u aty <*>
            extractTerm tyctx env b (times u' u) s
        _ -> Nothing

    MkTensor a b ->
      case ty of
        Tensor _ s t ->
          HsTmPair <$>
          extractTerm tyctx env a u s <*>
          extractTerm tyctx env b u (instantiate1Name (Ann a u s) t)
        _ -> Nothing
    Tensor{} -> Nothing
    UnpackTensor n1 n2 a b -> do
      aty <- infer env a u ^? _Right._3
      case aty of
        Tensor _ s t -> do
          a' <- extractTerm tyctx env a u s
          if isType s
            then do
              s' <- extractType tyctx s
              b' <-
                extractTerm
                  (unvar (bool s' HsTyUnit . extract) tyctx)
                  (deeperEnv
                     Name.name
                     (Just . BindingEntry .
                      bool s (instantiate1Name (Fst a) t) .
                      extract)
                     (const $ Just u)
                     env)
                  (fromScope b)
                  u
                  (F <$> ty)
              pure $
                case traverse (unvar (Left . HsTyVar . Name.name) Right) (fromScope t) of
                  Left{} ->
                    HsTmCase a'
                    [ ( HsPatCtor "TensorE"
                        [ HsPatProxy `HsPatAnn`
                          HsTyApp HsTyProxy s'
                        , HsPatVar n2
                        ]
                      , b'
                      )
                    ]
                  Right{} ->
                    HsTmCase a'
                    [ ( HsPatCtor "TensorP"
                        [ HsPatVar n1
                        , HsPatVar n2
                        ]
                      , b'
                      )
                    ]
            else do
              b' <-
                extractTerm
                  (unvar (const HsTyUnit) tyctx)
                  (deeperEnv
                     Name.name
                     (Just . BindingEntry .
                      bool s (instantiate1Name (Fst a) t) .
                      extract)
                     (const $ Just u)
                     env)
                  (fromScope b)
                  u
                  (F <$> ty)
              pure $
                HsTmCase a'
                [ ( HsPatCtor "TensorP"
                    [ HsPatVar n1
                    , HsPatVar n2
                    ]
                  , b'
                  )
                ]
        _ -> Nothing
    MkWith a b ->
      case ty of
        With _ s t ->
          HsTmPair <$>
          extractTerm tyctx env a u s <*>
          extractTerm tyctx env b u (instantiate1Name (Ann a u s) t)
        _ -> Nothing
    With{} -> Nothing
    Fst a ->
      fmap (HsTmApp HsTmFst) . extractTerm tyctx env a u =<<
      (infer env a u ^? _Right._3)
    Snd a ->
      fmap (HsTmApp HsTmSnd) . extractTerm tyctx env a u =<<
      (infer env a u ^? _Right._3)

    Unit -> Nothing
    MkUnit -> Just HsTmUnit

    Case{} -> undefined

    Loc _ a -> extractTerm tyctx env a u ty