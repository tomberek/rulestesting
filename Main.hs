{-# LANGUAGE QuasiQuotes     #-}
{-# LANGUAGE TemplateHaskell #-}
module Main where

import           Prelude                     hiding (id, (.))
import           Control.Arrow.Init.Optimize
import           Examples
import Criterion.Main

main :: IO ()
main = do
    printCCA example4b
    putStrLn ""
    printCCA ( $(normQ example4b) :: ASyn m Int Int)
    let banana = snd $(normOpt example4b)
    print $ banana (5::Int)
    printCCA example2
    putStrLn ""
    printCCA ($(normQ example2) :: ASyn m Int Int)
    putStrLn ""
    let b = snd $(normOpt example2)
    print $ b (5::Int)
    --runAutoIO_ a ("http://www.google.com","http://www.cnn.com") >>= print . show
    --(runKleisli . runPKleisli) banana ("http://www.google.com","http://www.cnn.com") >>= print . show
    --(runKleisli . runPKleisli) example2 ("http://www.google.com","http://www.cnn.com") >>= print . show
    print "hi"