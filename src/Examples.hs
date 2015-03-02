{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE Arrows #-}
module Examples where
import Parser
import Control.Arrow
import Debug.Trace

h :: Arrow a => a Int Int
h = [arrow|proc n -> arr (+1) -< n+2|]

f :: Int -> Int
f = [arrow|
    proc n -> do
    _ <- ((-)3) -< n
    returnA -< n+2
    |]
e :: Int -> Int
e = [arrow|
    proc n -> do
    Left a <- arr (\x -> Left x) -< n
    returnA -< a
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