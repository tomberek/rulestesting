{-# LANGUAGE QuasiQuotes     #-}
{-# LANGUAGE TemplateHaskell #-}
module Main where

import           Prelude                     hiding (id, (.))
import           Control.Arrow.Init.Optimize
import           Examples

main :: IO ()
main = do
    printCCA ( $(normQ example4b) :: ASyn m Int Int)
    --print $ snd $(normOpt example4b) (5::Int)
    printCCA ($(normQ example2) :: ASyn m Int Int)
    printCCA line2
    --printCCA ($(normQ line2) :: ASyn m (String,String) Int)
    --runAutoIO_ a ("http://www.google.com","http://www.cnn.com") >>= print . show
    --(runKleisli . runPKleisli) banana ("http://www.google.com","http://www.cnn.com") >>= print . show
    --(runKleisli . runPKleisli) example2 ("http://www.google.com","http://www.cnn.com") >>= print . show
    print "hi"
