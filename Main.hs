{-# LANGUAGE QuasiQuotes     #-}
{-# LANGUAGE TemplateHaskell #-}
module Main where

import           Prelude                     hiding (id, (.))
import           Control.Arrow.CCA.Optimize
import           Examples
import           Auto

main :: IO ()
main = do
    print "original:"
    printCCA example4b
    print "optimized:"
    printCCA ( $(normQ example4b))
    print ""
    print "original:"
    printCCA line2
    print "optimized:"
    printCCA ($(normQ line2))
    print "Autos running in parallel"
    runAutoIO_ line2 ("http://www.google.com","http://www.cnn.com") >>= print . show
    --(runKleisli . runPKleisli) banana ("http://www.google.com","http://www.cnn.com") >>= print . show
    --(runKleisli . runPKleisli) example2 ("http://www.google.com","http://www.cnn.com") >>= print . show
    print "hi"
