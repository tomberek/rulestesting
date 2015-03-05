{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE Arrows #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Examples
     where
import Parser
import Control.CCA

h :: ArrowInit a => a Int Int
h = [arrowExp|proc n -> arr (+1) -< n+2 |]

f :: ArrowInit a => a Int Int
f = [arrowExp|
    proc n -> do
        Just a  <- arr (+1) >>> arr (\x -> Just x) -< n
        let c = n+n
            d = 0
        b <- arr (*10) -< n +5
        returnA -< n+1
    |]
e :: ArrowInit a => a Int Int
e = [arrowExp|
    proc n -> do
        returnA -< 10*n
        returnA -< 20*n
    |]

nonLoop :: Int -> Int
(_,nonLoop) = [arrowExpOpt|
    proc n -> arr id -< n+2
    |]

--d :: ArrowInit a => a Int Int
d = [| [arrowExp|
        proc n -> do
        Just a <- arr (\x -> Just x) -< n
        returnA -< n
        _ <- arr (*2) -< n+1
        d <- arr (*2) -< a*1
        returnA -< n
            |] |]

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