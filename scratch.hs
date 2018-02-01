{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
module Main where

import Control.Monad (join)
main = print ()

data DT (m :: * -> *) a where
  E :: DT m a
  M :: DT m a -> DT m a -> DT m a
  A :: DT m (m a) -> DT m a

instance Functor m => Functor (DT m) where
  fmap f E = E
  fmap f (M g d) = M (fmap f g) (fmap f d)
  fmap f (A gg)  = A (fmap (fmap f) gg)

plug :: Monad m => DT m a -> a -> m a
plug E       x = return x
plug (M g d) x = plug g =<< plug d x
plug (A gg)  x = join (plug gg (return x))
