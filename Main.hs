{-# LANGUAGE QuasiQuotes     #-}
{-# LANGUAGE TemplateHaskell #-}
module Main where

import           Prelude                     hiding (id, (.))
import           Control.Arrow.CCA.Optimize
import           Examples
import           Auto
import Control.Category.Monoidal
main :: IO ()
main = do
    print a
    print b
    
    print "Just proc-do desugar:"
    printCCA example4b
    print "CCA optimized:"
    printCCA ( $(norm example4b))
    print ""
    print "Just proc-do desugar:"
    printCCA line3
    print "CCA optimized:"
    printCCA ( $(norm line3))
    print ""
    print "Just proc-do desugar:"
    printCCA line2
    print "CCA optimized:"
    printCCA ($(norm line2))
    print "Autos running in parallel"
    let a = $(norm line2) :: AutoXIO (String,String) Int
        b = runAutoIO_ a
    b ("http://www.google.com","http://www.cnn.com") >>= print . show
    --(runKleisli . runPKleisli) banana ("http://www.google.com","http://www.cnn.com") >>= print . show
    --(runKleisli . runPKleisli) example2 ("http://www.google.com","http://www.cnn.com") >>= print . show
    print "hi"
