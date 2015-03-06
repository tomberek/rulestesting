{-# LANGUAGE QuasiQuotes #-}
module Examples where
import Control.Arrow.Init.TH

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
