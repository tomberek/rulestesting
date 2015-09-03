{-# LANGUAGE QuasiQuotes     #-}
{-# LANGUAGE TemplateHaskell #-}
module Main where

import           Prelude                     hiding (id, (.))
import           Control.Arrow.CCA.Optimize
import           Examples
import           Auto

main :: IO ()
main = do
    --print "Just proc-do desugar:"
    --printCCA example4b
    --print "CCA optimized:"

    --printCCA ( $(norm example4b))
    --putStrLn ""
    --print "Just proc-do desugar:"
    printCCA line3a
    print "CCA optimized:"
    printCCA ( $(norm line3a))
    --putStrLn ""
    --print "Just proc-do desugar:"
    --printCCA line2
    --print "CCA optimized:"
    --printCCA ($(norm line2))
    --print "Autos running in parallel"
    --let a = $(norm line2) :: AutoXIO (String,String) Int
    --    b = runAutoIO_ a
    --b ("http://www.google.com","http://www.cnn.com") >>= print . show
    --(runKleisli . runPKleisli) banana ("http://www.google.com","http://www.cnn.com") >>= print . show
    --(runKleisli . runPKleisli) example2 ("http://www.google.com","http://www.cnn.com") >>= print . show
    --print "hi"
