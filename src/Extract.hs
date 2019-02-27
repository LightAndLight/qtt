module Extract where

import Bound.Name (instantiate1Name)
import Bound.Scope (fromScope)
import Bound.Var (Var(..))
import Control.Comonad (extract)
import Control.Lens.Fold ((^?))
import Control.Lens.Getter (view)
import Control.Lens.Prism (_Right)
import Control.Lens.Tuple (_3)
import Data.Bool (bool)
import Data.Semiring (times)
import Text.PrettyPrint.ANSI.Leijen (Pretty(..))

import qualified Bound.Name as Name
import qualified Text.PrettyPrint.ANSI.Leijen as Pretty

import Context
import Syntax
import Typecheck

data HsPat a
  = HsPatPair (HsPat a) (HsPat a)
  | HsPatVar a
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
data HsTy a
  = HsTyUnit
  | HsTyProxy (HsTy a)
  | HsTyVar a

instance Pretty a => Pretty (HsPat a) where
  pretty pat =
    case pat of
      HsPatWild -> Pretty.char '_'
      HsPatVar a -> pretty a
      HsPatPair a b ->
        Pretty.parens $
        pretty a <> Pretty.comma <> Pretty.space <> pretty b

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
             _ -> id)
          (pretty a)
        , (case b of
             HsTmApp{} -> Pretty.parens
             HsTmLet{} -> Pretty.parens
             HsTmLam{} -> Pretty.parens
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
      HsTmLam a b -> Pretty.char '\\' <> Pretty.hsep [pretty a, Pretty.text "->", pretty b]
      HsTmProxy -> Pretty.text "proxy#"

{-
extractType :: Term a l a -> Maybe (HsTy a)
extractType tm ty =
  case tm of
    Var a
    Ann (Term n l a) Usage (Term n l a)
    Type

    Lam n (Scope (Name n ()) (Term n l) a)
    Pi Usage (Maybe n) (Term n l a) (Scope (Name n ()) (Term n l) a)
    App (Term n l a) (Term n l a)

    MkTensor (Term n l a) (Term n l a)
    Tensor n (Term n l a) (Scope (Name n ()) (Term n l) a)
    UnpackTensor n n (Term n l a) (Scope (Name n Bool) (Term n l) a)

    MkWith (Term n l a) (Term n l a)
    With n (Term n l a) (Scope (Name n ()) (Term n l) a)
    Fst (Term n l a)
    Snd (Term n l a)

    Unit -> Right $ HsTyUnit
    MkUnit -> Left ()

    Case a b -> _

    Loc _ a -> extraction a ty
-}

extractTerm ::
  (Ord x, Ord a) =>
  Env a l x ->
  Term a l x ->
  Usage ->
  Ty a l x ->
  Maybe (HsTm a)
extractTerm env tm u ty =
  case tm of
    Var a -> do
      usage <- view envUsages env a
      pure $
        case usage of
          Zero -> HsTmProxy
          _ -> HsTmVar $ view envNames env a
    Ann a u' b -> extractTerm env a u' b
    Type -> Nothing

    Lam n a ->
      case ty of
        Pi u' _ s t ->
          HsTmLam (case u' of; Zero -> HsPatWild; _ -> HsPatVar n) <$>
          extractTerm
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
            extractTerm env a u aty <*>
            extractTerm env b (times u' u) s
        _ -> Nothing

    MkTensor a b ->
      case ty of
        Tensor _ s t ->
          HsTmPair <$>
          extractTerm env a u s <*>
          extractTerm env b u (instantiate1Name (Ann a u s) t)
        _ -> Nothing
    Tensor{} -> Nothing
    UnpackTensor n1 n2 a b -> do
      aty <- infer env a u ^? _Right._3
      case aty of
        Tensor _ s t ->
          HsTmLet (HsPatPair (HsPatVar n1) (HsPatVar n2)) <$>
            extractTerm env a u aty <*>
            extractTerm
              (deeperEnv
                 Name.name
                 (Just . BindingEntry . bool s (instantiate1Name (Fst a) t) . extract)
                 (const $ Just u)
                 env)
              (fromScope b)
              u
              (F <$> ty)
        _ -> Nothing
    MkWith a b ->
      case ty of
        With _ s t ->
          HsTmPair <$>
          extractTerm env a u s <*>
          extractTerm env b u (instantiate1Name (Ann a u s) t)
        _ -> Nothing
    With{} -> Nothing
    Fst a -> fmap (HsTmApp HsTmFst) . extractTerm env a u =<< (infer env a u ^? _Right._3)
    Snd a -> fmap (HsTmApp HsTmSnd) . extractTerm env a u =<< (infer env a u ^? _Right._3)

    Unit -> Nothing
    MkUnit -> Just HsTmUnit

    Case{} -> undefined

    Loc _ a -> extractTerm env a u ty