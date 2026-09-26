{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Prolog.Programming.TypeHelper (recordFieldNames) where

import Data.Kind (Type)
import Data.Proxy (Proxy (..))
import GHC.Generics (
  C,
  D,
  Generic (Rep),
  K1,
  M1,
  Meta (..),
  S,
  U1,
  type (:*:),
 )
import GHC.TypeLits (KnownSymbol, symbolVal)

class FieldNames (f :: Type -> Type) where
  fieldNames :: [String]

instance FieldNames U1 where
  fieldNames = []

instance
  KnownSymbol name
  => FieldNames (M1 S ('MetaSel ('Just name) su ss ds) (K1 i c))
  where
  fieldNames = [symbolVal (Proxy @name)]

instance (FieldNames l, FieldNames r) => FieldNames (l :*: r) where
  fieldNames = fieldNames @l ++ fieldNames @r

instance FieldNames f => FieldNames (M1 C c f) where
  fieldNames = fieldNames @f

instance FieldNames f => FieldNames (M1 D d f) where
  fieldNames = fieldNames @f

recordFieldNames
  :: forall a. (FieldNames (Rep a), Generic a) => [String]
recordFieldNames = fieldNames @(Rep a)
