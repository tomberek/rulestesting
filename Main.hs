{-# LANGUAGE QuasiQuotes     #-}
{-# LANGUAGE TemplateHaskell #-}
module Main where

import           Control.Category
import           Prelude                     hiding (id, (.))

--import           Auto
import           Control.Arrow
import Control.Applicative
import           Control.Arrow.Init
import           Control.Arrow.Init.Optimize
import           Control.Arrow.TH
import           Examples

main :: IO ()
main = do
    printCCA line3
    putStrLn ""
    printCCA $(normFixed line3)
    putStrLn ""
    let banana = snd $(normOpt line3)
    --runAutoIO_ a ("http://www.google.com","http://www.cnn.com") >>= print . show
    (runKleisli . runPKleisli) banana ("http://www.google.com","http://www.cnn.com") >>= print . show
    print "hi"
    
{-}
exampleOpt :: (Int, ((), Int) -> (Int, Int))
exampleOpt = [arrowOpt|
    proc () -> do
        rec a <- init (1::Int) -< b *10
            b <- arr (+4) -< a
        returnA -< a
        |]
complexA :: Int -> (Int,Int)
(_,complexA) = [arrowOpt|
    proc n -> do
        a <- arr (+5) -< n - (4::Int)
        c <- arr (*10) -< a +n
        d <- arr (+1) >>> arr (+43) -< a + c
        returnA -< (c,a)
        |]


---}
---}
