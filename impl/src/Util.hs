{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
module Util where

import Data.Bifunctor

data NEList a
  = Done a
  | Cons a (NEList a)
  deriving (Show, Read, Eq, Functor, Foldable, Traversable)

toNE :: [a] -> Maybe (NEList a)
toNE = foldr cons Nothing
  where cons :: a -> Maybe (NEList a) -> Maybe (NEList a)
        cons x   Nothing = Just (Done x)
        cons x (Just xs) = Just (Cons x xs)

neFold :: (a -> b -> b) -> (a -> b) -> NEList a -> b
neFold cons done (Done x)    = done x
neFold cons done (Cons x xs) = cons x (neFold cons done xs)

neHd :: NEList a -> a
neHd (Done x)   = x
neHd (Cons x _) = x

firstAndLast :: NEList a -> (a, a)
firstAndLast = neFold cons done
  where done x = (x,x)
        cons first (_,last) = (first, last)

data ConsStar a b
  = DoneB b
  | ConsA a (ConsStar a b)
  deriving (Show, Eq)

instance Bifunctor ConsStar where
  bimap fa fb = go
    where go (DoneB b) = DoneB (fb b)
          go (ConsA a rest) = ConsA (fa a) (go rest)

allAs :: ConsStar a b -> [a]
allAs (DoneB _)      = []
allAs (ConsA a rest) = a : allAs rest


consStartoNE :: ConsStar a a -> NEList a
consStartoNE (DoneB a) = Done a
consStartoNE (ConsA a rest) = Cons a (consStartoNE rest)

