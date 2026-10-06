module Prolog.Programming.Helper where

import Data.Data (Data)
import Data.Generics (everywhere, mkT)
import Language.Prolog (Atom, Term (..))
import Prolog.Programming.CodeAnalysis.Types (Severity (..))

type Arity = Int
termHead :: Term -> (Atom, Arity)
termHead (Struct hd args) = (hd, length args)
termHead _ = error "can't extract clause head"

escalateSeverity :: Data a => a -> a
escalateSeverity = everywhere $ mkT toError
  where
    toError :: Severity -> Severity
    toError _ = Error
