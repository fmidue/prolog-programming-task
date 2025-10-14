{-# LANGUAGE CPP #-}
#if !MIN_VERSION_base(4,18,0)
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DerivingStrategies #-}
#endif
{-# LANGUAGE DeriveGeneric #-}
module Prolog.Programming.Data where

#if !MIN_VERSION_base(4,18,0)
import Data.Typeable                    (Typeable)
#endif
import GHC.Generics                     (Generic)

newtype Code = Code String
  deriving (Eq, Generic, Ord, Read, Show)
#if !MIN_VERSION_base(4,18,0)
  deriving Typeable
#endif

newtype Config = Config String
  deriving (Eq, Generic, Ord, Read, Show)
#if !MIN_VERSION_base(4,18,0)
  deriving Typeable
#endif
