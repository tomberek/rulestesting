{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE Arrows #-}
module Examples where
import Control.Arrow.Init.TH
import Control.Arrow.Init.Optimize
import Control.Arrow
temp f = [| $(temp3 f) |]
t = temp3

temp2 :: ArrowInit a => a Int Int
temp2 = [arrowTest| arr (+1) >>> arr (+2) |]

example0 :: ArrowInit a => a Int Int
example0 = [arrow|proc n -> arr (+1) -< n+2 |]

example1 :: ArrowInit a => a Int Int
example1 = [arrow|
    proc n -> do
        Just a  <- arr (\x -> Just x) -< (n::Int)
        rec
                e <- arr id -< a + (1::Int)
                f <- arr id -< a - n
                g <- arr id -< "aerfa"
        returnA -< length g
    |]
example2 :: ArrowInit a => a Int Int
example2 = [arrow|
    proc n -> do
        returnA -< 10*n
        returnA -< 20*n
    |]

example3 :: Int -> Int
(_,example3) = [arrowOpt|
    proc n -> arr id -< n+2
    |]

example4 :: ArrowInit a => a Int Int
example4 = [arrow|
        proc n -> do
        Just a <- arr (\x -> Just x) -< n
        returnA -< n
        _ <- arr (*2) -< n+1
        d <- arr (*2) -< a*1
        returnA -< n
            |]

{-
i = [arrow|
    proc n -> do
        x <- id -< n + n
        y <- arr (+1) -< x
        let z = x + y
        returnA -< z
        |]

---}
---}
