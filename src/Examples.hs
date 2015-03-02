{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE Arrows #-}
module Examples where
import Parser
import Control.Arrow

h :: Arrow a => a Int Int
h = [arrow|proc n -> arr (+1) -< n+2|]

f :: Int -> Int
f = [arrow|
    proc n -> do
    returnA -< n+2
    |]
--e :: Int -> Int
e = [arrow|
    proc n -> do
    a <- (+1) -< n
    b <- (+2) -< a
    id -< (a,b+2)
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