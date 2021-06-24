{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
module Prolog.Programming.Data where

import Data.Typeable                    (Typeable)
import GHC.Generics                     (Generic)

newtype Code = Code String
  deriving (Eq, Generic, Ord, Read, Show, Typeable)

newtype Config = Config String
  deriving (Eq, Generic, Ord, Read, Show, Typeable)
