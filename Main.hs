{-# LANGUAGE QuasiQuotes     #-}
{-# LANGUAGE TemplateHaskell #-}
module Main where

import           Prelude                     hiding (id, (.))
import           Control.Arrow.CCA.Optimize
import           Examples
import Auto
main :: IO ()
main = do
    printCCA ( $(normQ example4b))
    --print $ snd $(normOpt example4b) (5::Int)
    printCCA ($(normQ example2) )
    --printCCA ($(normQ line2))
    --runAutoIO_ line2 ("http://www.google.com","http://www.cnn.com") >>= print . show
    --(runKleisli . runPKleisli) banana ("http://www.google.com","http://www.cnn.com") >>= print . show
    --(runKleisli . runPKleisli) example2 ("http://www.google.com","http://www.cnn.com") >>= print . show
    print "hi"
