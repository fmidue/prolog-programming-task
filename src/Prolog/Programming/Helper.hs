module Prolog.Programming.Helper where

import Language.Prolog (Atom, Term(..))

type Arity = Int
termHead :: Term -> (Atom,Arity)
termHead (Struct hd args) = (hd, length args)
termHead _ = error "can't extract clause head"
