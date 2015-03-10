{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
module Examples where
import Control.Arrow.TH
import Control.Arrow.Init.Optimize
import Control.Arrow

example1 :: ArrowInit a => a Int Int
example1 = [arrowTH|
    proc n -> do
        a  <- arr (\x -> x) -< (n::Int)
        rec
            e <- arr (+1) -< a + (1::Int)
        returnA -< a
    |]


{-
example4 :: ArrowInit a => a Int Int
example4 = [arrow|
     proc n -> do
        a <- arr (+1) -< n
        returnA -< n
        _ <- arr (*2) -< n+1
        d <- arr (*2) -< a*1
        returnA -< n
            |]

example2 :: ArrowInit a => a Int Int
example2 = [arrowTH|
    proc n -> do
        returnA -< 10*n
    |]
temp2 :: ASyn m Int Int
temp2 = [arrowTH| arr (\a -> (a+3)) >>> arr (+2) |]

example0 :: ArrowInit a => a Int Int
example0 = [arrowTH|proc n -> arr (+1) -< n+2 |]


example3 :: Int -> Int
(_,example3) = $(normOpt [arrowTH|
    proc n -> arr id -< n+2
    |] )

i = [arrow|
    proc n -> do
        x <- id -< n + n
        y <- arr (+1) -< x
        let z = x + y
        returnA -< z
        |]

---}
---}
