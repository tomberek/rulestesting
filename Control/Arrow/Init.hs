{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE CPP #-}
-- originally from CCA package: https://hackage.haskell.org/package/CCA-0.1.5.2
module Control.Arrow.Init where

import Control.Category

import Control.Arrow
import Language.Haskell.TH

import Prelude hiding (init)

class (Arrow a, ArrowLoop a) => ArrowInit a where
  init :: b -> a b b
  init' :: ExpQ -> b -> a b b
  init' _ = init
  arr' :: ExpQ -> (b->c) -> a b c
  arr' _ = arr
  loopD :: e -> ((b, e) -> (c, e)) -> a b c
  loopD i f = loop (arr f >>> second (init i))

class Monad m => ArrowMonad a m where
    arrM :: (b -> m c) -> a m b c
    arrM' :: ExpQ -> (b -> m c) -> a m b c
    arrM' _ = arrM


