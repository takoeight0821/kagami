module Language.Malgo.Type where

import           Data.String
import           Language.Malgo.Utils
import           Text.PrettyPrint

-- | Malgoの組み込みデータ型
data Type = NameTy Name
          -- | TupleTy [Type]
          | FunTy { _params :: [Type]
                  , _ret    :: Type
                  }
          | ClsTy { _params   :: [Type]
                  , _ret      :: Type
                  , _captures :: [Type]
                  }
  deriving (Eq, Show, Ord)

instance PrettyPrint Type where
  pretty (NameTy n)          = pretty n
  -- pretty (TupleTy types)     = parens (cat $ punctuate (text ",") $ map pretty types)
  pretty (FunTy param ret) =
    parens (cat (punctuate (text ",") (map pretty param))
    <+> text "->" <+> pretty ret)
  pretty (ClsTy param ret cap) = braces
    (parens (cat (punctuate (text ",") (map pretty param))
             <+> text "->" <+> pretty ret))
    <+> brackets (sep (map pretty cap))

instance IsString Type where
  fromString name = NameTy $ fromString name

class Typeable a where
  typeOf :: a -> Type