{-# LANGUAGE QuasiQuotes     #-}
{-# LANGUAGE TemplateHaskell #-}
module Main where


import           Prelude                     hiding (id, (.))

--import           Auto



import           Control.Arrow.Init.Optimize

import           Examples

main :: IO ()
main = do
    printCCA example4
    putStrLn ""
    printCCA $(normFixed example4)
    putStrLn ""
    printCCA ( $(normFixed example4b) :: ASyn m Int Int)
    let banana = snd $(normOpt example4b)
    print $ banana (5::Int)
    printCCA example2
    putStrLn ""
    printCCA ($(normFixed example2) :: ASyn m Int Int)
    putStrLn ""
    let b = snd $(normOpt example2)
    print $ b (5::Int)
    
    --runAutoIO_ a ("http://www.google.com","http://www.cnn.com") >>= print . show
    --(runKleisli . runPKleisli) banana ("http://www.google.com","http://www.cnn.com") >>= print . show
    --(runKleisli . runPKleisli) example2 ("http://www.google.com","http://www.cnn.com") >>= print . show
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
