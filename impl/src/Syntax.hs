{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE TemplateHaskell #-}
module Syntax where

import Control.Lens
import qualified Text.Parsec as Parsec

import Util

-- | Raw S-expressions, the output of the parser.
data ParsedSExp = ParsedSExp { _loc :: Parsec.SourcePos, _sexp :: SExp }
  deriving (Show)

data SExp
  = SEAtom String
  | SEList [ParsedSExp]
  deriving (Show)

data Decl name a = Decl { _name :: name , _defn :: a }
  deriving (Show, Read, Eq, Functor)

$(makeLenses ''Decl)

type SynDecl = Decl String

lookupDecl :: (Eq name) => name -> [Decl name a] -> Maybe a
lookupDecl s xs = lookup s (map declToPair xs)
  where
    declToPair :: Decl name a -> (name, a)
    declToPair d = (_name d, _defn d)
