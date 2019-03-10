{-# language OverloadedStrings #-}
{-# language ScopedTypeVariables #-}
module Extract where

import Bound.Name (instantiate1Name)
import Bound.Scope (Scope, fromScope)
import Bound.Var (Var(..), unvar)
import Control.Comonad (extract)
import Control.Lens.Getter (view)
import Data.Bifunctor (first)
import Data.Bool (bool)
import Data.Semiring (times)
import Data.String (IsString)
import Data.Text (Text)
import Text.PrettyPrint.ANSI.Leijen (Pretty(..), Doc)

import qualified Bound.Name as Name
import qualified Data.Map as Map
import qualified Data.Text as Text
import qualified Text.PrettyPrint.ANSI.Leijen as Pretty

import Context
import Inductive
import Syntax
import TypeError
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
  | HsTyVoid
  | HsTyProxy
  | HsTyVar a
  | HsTyApp (HsTy a) (HsTy a)
  | HsTyForall a (HsTy a)
  | HsTyCtor Text
  | HsArr (HsTy a) (HsTy a)
data HsKind = HsKindStar | HsKindArr HsKind HsKind
data HsDef n a
  = HsDefGADT n HsKind [(n, HsTy a)]
  | HsDefValue a (HsTm a)

karr_ :: HsKind -> HsKind -> HsKind
karr_ = HsKindArr

kstar_ :: HsKind
kstar_ = HsKindStar

instance Pretty HsKind where
  pretty HsKindStar = Pretty.char '*'
  pretty (HsKindArr a b) =
    Pretty.hsep
    [ (case a of
         HsKindArr{} -> Pretty.parens
         _ -> id)
      (pretty a)
    , Pretty.text "->"
    , pretty b
    ]

instance Pretty a => Pretty (HsPat a) where
  pretty = prettyHsPat pretty

prettyHsPat :: (a -> Doc) -> HsPat a -> Doc
prettyHsPat pvar pat =
  case pat of
    HsPatWild -> Pretty.char '_'
    HsPatVar a -> pvar a
    HsPatCtor a b ->
      Pretty.hsep $
      Pretty.text (Text.unpack a) :
      fmap
        (\x ->
            (case x of
              HsPatCtor{} -> Pretty.parens
              HsPatAnn{} -> Pretty.parens
              _ -> id)
            (prettyHsPat pvar x))
        b
    HsPatAnn a b ->
      Pretty.hsep
      [prettyHsPat pvar a, Pretty.text "::", prettyHsTy pvar b]
    HsPatProxy -> Pretty.text "proxy#"

prettyHsTm :: (a -> Doc) -> HsTm a -> Doc
prettyHsTm pvar tm =
  case tm of
    HsTmUnit -> Pretty.text "()"
    HsTmFst -> Pretty.text "fst"
    HsTmSnd -> Pretty.text "snd"
    HsTmPair a b ->
      Pretty.parens $
      prettyHsTm pvar a <> Pretty.comma <> Pretty.space <>
      prettyHsTm pvar b
    HsTmApp a b ->
      Pretty.hsep
      [ (case a of
            HsTmLet{} -> Pretty.parens
            HsTmLam{} -> Pretty.parens
            HsTmAnn{} -> Pretty.parens
            _ -> id)
        (prettyHsTm pvar a)
      , (case b of
            HsTmApp{} -> Pretty.parens
            HsTmLet{} -> Pretty.parens
            HsTmLam{} -> Pretty.parens
            HsTmAnn{} -> Pretty.parens
            _ -> id)
        (prettyHsTm pvar b)
      ]
    HsTmLet a b c ->
      Pretty.hsep
      [ Pretty.text "let"
      , prettyHsPat pvar a
      , Pretty.char '='
      , (case b of
            HsTmLet{} -> Pretty.parens
            _ -> id)
        (prettyHsTm pvar b)
      , Pretty.text "in"
      ] Pretty.<$>
      prettyHsTm pvar c
    HsTmVar a -> pvar a
    HsTmLam a b ->
      Pretty.char '\\' <>
      Pretty.hsep
      [ (case a of
            HsPatCtor{} -> Pretty.parens
            HsPatAnn{} -> Pretty.parens
            _ -> id)
        (prettyHsPat pvar a)
      , Pretty.text "->"
      , prettyHsTm pvar b
      ]
    HsTmProxy -> Pretty.text "proxy#"
    HsTmCase a b ->
      Pretty.hsep
      [ Pretty.text "case"
      , prettyHsTm pvar a
      , Pretty.text "of"
      ] Pretty.<$>
      Pretty.indent 2
      (Pretty.vsep $
        fmap
          (\(x, y) ->
            Pretty.hsep
            [ prettyHsPat pvar x
            , Pretty.text "->"
            , prettyHsTm pvar y
            ])
          b)
    HsTmAnn a b ->
      Pretty.hsep
      [ (case a of
            HsTmLam{} -> Pretty.parens
            HsTmCase{} -> Pretty.parens
            HsTmLet{} -> Pretty.parens
            _ -> id)
        (prettyHsTm pvar a)
      , Pretty.text "::"
      , prettyHsTy pvar b
      ]

instance Pretty a => Pretty (HsTm a) where
  pretty = prettyHsTm pretty

prettyHsTy :: (a -> Doc) -> HsTy a -> Doc
prettyHsTy pvar ty =
  case ty of
    HsArr a b ->
      Pretty.hsep
      [ (case a of
            HsArr{} -> Pretty.parens
            _ -> id)
        (prettyHsTy pvar a)
      , Pretty.text "->"
      , prettyHsTy pvar b
      ]
    HsTyUnit -> Pretty.text "()"
    HsTyVoid -> Pretty.text "Void"
    HsTyProxy -> Pretty.text "Proxy#"
    HsTyVar a -> pvar a
    HsTyApp a b ->
      Pretty.hsep
      [ (case a of
            HsTyForall{} -> Pretty.parens
            _ -> id)
        (prettyHsTy pvar a)
      , (case b of
            HsTyApp{} -> Pretty.parens
            HsTyForall{} -> Pretty.parens
            _ -> id)
        (prettyHsTy pvar b)
      ]
    HsTyForall a b ->
      Pretty.hsep
      [ Pretty.text "forall"
      , pvar a <> Pretty.dot
      , prettyHsTy pvar b
      ]
    HsTyCtor a -> Pretty.text $ Text.unpack a

instance Pretty a => Pretty (HsTy a) where
  pretty = prettyHsTy pretty

prettyHsDef :: (n -> Doc) -> (a -> Doc) -> HsDef n a -> Doc
prettyHsDef pname pvar def =
  case def of
    HsDefValue a b ->
      Pretty.hsep [pvar a, Pretty.char '='] Pretty.<$>
      Pretty.indent 2 (prettyHsTm pvar b)
    HsDefGADT a b c ->
      Pretty.hsep
        [ Pretty.text "data"
        , pname a
        , Pretty.text "::"
        , pretty b
        , Pretty.text "where"
        ] Pretty.<$>
      Pretty.indent 2
      (Pretty.vsep $
        fmap
          (\(d, e) ->
            Pretty.hsep
            [ pname d
            , Pretty.text "::"
            , prettyHsTy pvar e
            ])
          c)

instance (Pretty n, Pretty a) => Pretty (HsDef n a) where
  pretty = prettyHsDef pretty pretty

prelude :: (IsString n, IsString a) => [HsDef n a]
prelude =
  [ HsDefGADT "TensorE" (karr_ (karr_ kstar_ kstar_) kstar_)
    [ ( "TensorE"
      , HsArr (HsTyApp HsTyProxy (HsTyVar "a")) $
        HsArr (HsTyApp (HsTyVar "f") (HsTyVar "a")) $
        HsTyApp (HsTyCtor "TensorE") (HsTyVar "f")
      )
    ]
  , HsDefGADT "TensorP" (karr_ kstar_ $ karr_ kstar_ kstar_)
    [ ( "TensorP"
      , HsArr (HsTyVar "a") $
        HsArr (HsTyVar "b") $
        HsTyApp (HsTyApp (HsTyCtor "TensorP") (HsTyVar "a")) (HsTyVar "b")
      )
    ]
  , HsDefGADT "WithE" (karr_ (karr_ kstar_ kstar_) kstar_)
    [ ( "WithE"
      , HsArr (HsTyApp HsTyProxy (HsTyVar "a")) $
        HsArr (HsTyApp (HsTyVar "f") (HsTyVar "a")) $
        HsTyApp (HsTyCtor "WithE") (HsTyVar "f")
      )
    ]
  , HsDefGADT "WithP" (karr_ kstar_ $ karr_ kstar_ kstar_)
    [ ( "WithP"
      , HsArr (HsTyVar "a") $
        HsArr (HsTyVar "b") $
        HsTyApp (HsTyApp (HsTyCtor "WithP") (HsTyVar "a")) (HsTyVar "b")
      )
    ]
  , HsDefValue "fst" $
    HsTmLam (HsPatCtor "WithP" [HsPatVar "a", HsPatWild]) (HsTmVar "a")
  , HsDefValue "snd" $
    HsTmLam (HsPatCtor "WithP" [HsPatWild, HsPatVar "b"]) (HsTmVar "b")
  ]

data Sort = SortTerm | SortType | SortKind
  deriving Show

data ExtractError l a
  = TypeError (TypeError l a)
  | SortMismatch Sort Sort (Term a l a)
  deriving Show

extractType ::
  forall a l x.
  (Ord a, Ord x) =>
  Env a l x ->
  (x -> HsTy a) ->
  Term a l x ->
  Either (ExtractError l a) (HsTy a)
extractType env depth ty =
  case ty of
    Var a -> pure $ depth a
    Ann a _ _ -> extractType env depth a
    Type ->
      Left .
      SortMismatch SortType SortKind $
      fmap (view envNames env) ty
    Lam{} ->
      Left .
      SortMismatch SortType SortTerm $
      fmap (view envNames env) ty
    Pi u a b c ->
      let
        entry = const $ Just $ BindingEntry b
      in
        case b of
          Type ->
            case u of
              Zero ->
                HsArr (HsTyApp HsTyProxy $ maybe HsTyVoid HsTyVar a) <$>
                extractType
                  (deeperEnv
                     Name.name
                     entry
                     (const $ Just Zero)
                     env)
                  (unvar (HsTyVar . Name.name) depth)
                  (fromScope c)
              _ -> error "typerep not supported"
          _ -> do
            c' <-
              extractType
                (deeperEnv
                   Name.name
                   entry
                   (const $ Just Zero)
                   env)
                (unvar (const HsTyVoid) depth)
                (fromScope c)
            case u of
              Zero -> pure $ HsArr (HsTyApp HsTyProxy HsTyVoid) c'
              _ ->
                HsArr <$>
                extractType env depth b <*>
                pure c'
    App a b -> do
      (_, _, appty) <- first TypeError $ infer env a Zero
      case appty of
        Pi _ _ s _ ->
          if isType s
          then
            HsTyApp <$>
            extractType env depth a <*>
            extractType env depth b
          else
            HsTyApp <$>
            extractType env depth a <*>
            pure HsTyVoid
        _ ->
          Left . TypeError $
          ExpectedPi (view envNames env <$> appty)
    MkTensor{} ->
      Left .
      SortMismatch SortType SortTerm $
      fmap (view envNames env) ty
    Tensor _ a b -> genProduct "Tensor" a b
    UnpackTensor{} ->
      Left .
      SortMismatch SortType SortTerm $
      fmap (view envNames env) ty
    MkWith{} ->
      Left .
      SortMismatch SortType SortTerm $
      fmap (view envNames env) ty
    With _ a b -> genProduct "With" a b
    Fst{} ->
      Left .
      SortMismatch SortType SortTerm $
      fmap (view envNames env) ty
    Snd{} ->
      Left .
      SortMismatch SortType SortTerm $
      fmap (view envNames env) ty

    Unit -> pure HsTyUnit
    MkUnit ->
      Left .
      SortMismatch SortType SortTerm $
      fmap (view envNames env) ty

    Case{} ->
      Left .
      SortMismatch SortType SortTerm $
      fmap (view envNames env) ty

    Loc _ a -> extractType env depth a
  where
    genProduct ::
      Text ->
      Term a l x ->
      Scope (Name.Name a ()) (Term a l) x ->
      Either (ExtractError l a) (HsTy a)
    genProduct name a b =
      case a of
        Type ->
          case traverse (unvar (Left . HsTyVar . Name.name) Right) (fromScope b) of
            Left x -> pure $ HsTyApp (HsTyCtor $ name <> "E") x
            Right x ->
              HsTyApp <$>
              (HsTyApp (HsTyCtor $ name <> "P") <$>
               extractType env depth a) <*>
              extractType env depth x
        _ ->
          HsTyApp <$>
          (HsTyApp (HsTyCtor $ name <> "P") <$>
           extractType env depth a) <*>
          extractType
            (deeperEnv
               Name.name
               (const $ Just $ BindingEntry a)
               (const $ Just Zero)
               env)
            (unvar (const HsTyUnit) depth)
            (fromScope b)

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
  Either (ExtractError l a) (HsTm a)
extractTerm tyctx env tm u ty =
  case tm of
    Var a -> do
      usage <-
        maybe
          (Left . TypeError . NotInScope $ view envNames env a)
          pure
          (view envUsages env a)
      pure $
        case usage of
          Zero -> HsTmProxy
          _ -> HsTmVar $ view envNames env a
    Ann a u' b -> extractTerm tyctx env a u' b
    Type ->
      Left .
      SortMismatch SortTerm SortKind $
      fmap (view envNames env) ty
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
        _ ->
          Left . TypeError . ExpectedPi $
          view envNames env <$> ty
    Pi{} ->
      Left .
      SortMismatch SortTerm SortType $
      fmap (view envNames env) ty
    App a b -> do
      (_, _, aty) <- first TypeError $ infer env a u
      case aty of
        Pi u' _ s _ ->
          HsTmApp <$>
            extractTerm tyctx env a u aty <*>
            extractTerm tyctx env b (times u' u) s
        _ ->
          Left . TypeError . ExpectedPi $
          view envNames env <$> aty
    MkTensor a b ->
      case ty of
        Tensor _ s t ->
          HsTmPair <$>
          extractTerm tyctx env a u s <*>
          extractTerm tyctx env b u (instantiate1Name (Ann a u s) t)
        _ ->
          Left . TypeError . ExpectedTensor $
          view envNames env <$> ty
    Tensor{} ->
      Left .
      SortMismatch SortTerm SortType $
      fmap (view envNames env) ty
    UnpackTensor n1 n2 a b -> do
      (_, _, aty) <- first TypeError $ infer env a u
      case aty of
        Tensor _ s t -> do
          a' <- extractTerm tyctx env a u s
          if isType s
            then do
              s' <- extractType env tyctx s
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
        _ ->
          Left . TypeError . ExpectedTensor $
          view envNames env <$> aty
    MkWith a b ->
      case ty of
        With _ s t ->
          HsTmPair <$>
          extractTerm tyctx env a u s <*>
          extractTerm tyctx env b u (instantiate1Name (Ann a u s) t)
        _ ->
          Left . TypeError . ExpectedWith $
          view envNames env <$> ty
    With{} ->
      Left .
      SortMismatch SortTerm SortType $
      fmap (view envNames env) ty
    Fst a -> do
      (_, _, aty) <- first TypeError $ infer env a u
      a' <- extractTerm tyctx env a u aty
      pure $ HsTmApp HsTmFst a'
    Snd a -> do
      (_, _, aty) <- first TypeError $ infer env a u
      a' <- extractTerm tyctx env a u aty
      pure $ HsTmApp HsTmSnd a'
    Unit ->
      Left .
      SortMismatch SortTerm SortType $
      fmap (view envNames env) ty
    MkUnit -> pure HsTmUnit

    Case{} -> undefined

    Loc _ a -> extractTerm tyctx env a u ty

isKind :: Term a l x -> Bool
isKind ty =
  case ty of
    Var{} -> False
    Ann a _ _ -> isKind a
    Type -> True

    Lam{} -> False
    Pi _ _ a b -> isKind a && isKind (fromScope b)
    App{} -> False

    MkTensor{} -> False
    Tensor{} -> False
    UnpackTensor{} -> False

    MkWith{} -> False
    With{} -> False
    Fst{} -> False
    Snd{} -> False

    Unit{} -> False
    MkUnit{} -> False

    Case{} -> False

    Loc _ a -> isKind a

extractKind :: Term a l x -> HsKind
extractKind ty =
  case ty of
    Var{} -> kstar_
    Ann a _ _ -> extractKind a
    Type -> kstar_

    Lam{} -> kstar_
    Pi _ _ a b ->
      (if isKind a then extractKind a else kstar_) `karr_`
      extractKind (fromScope b)
    App{} -> kstar_

    MkTensor{} -> kstar_
    Tensor{} -> kstar_
    UnpackTensor{} -> kstar_

    MkWith{} -> kstar_
    With{} -> kstar_
    Fst{} -> kstar_
    Snd{} -> kstar_

    Unit{} -> kstar_
    MkUnit{} -> kstar_

    Case{} -> kstar_

    Loc _ a -> extractKind a

extractInductive ::
  Ord a =>
  Env a l a ->
  Inductive a l a ->
  Either (ExtractError l a) (HsDef a a)
extractInductive env ind =
  HsDefGADT name (extractKind $ _indTypeType ind) <$>
  (Map.foldrWithKey
    (\k a b -> do
       a' <- extractType (extendEnv (inductiveEntry ind) env) HsTyVar a
       b' <- b
       pure $ (k, a') : b')
    (pure [])
    (_indConstructors ind))
  where
    name = _indTypeName ind
