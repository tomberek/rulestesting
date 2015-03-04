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
h = [arrow|proc n -> arr (+1) -< n+2 |]

f :: ArrowInit a => a Int Int
f = [arrow|
    proc n -> do
        Just a  <- arr (+1) >>> arr (\x -> Just x) -< n
        let c = a+a
            d = 0
        b <- arr (*10) -< a +5
        returnA -< d+1
    |]
e :: ArrowInit a => a Int Int
e = [arrow|
    proc n -> do
        returnA -< 10*n
        returnA -< 20*n
    |]
--d :: ArrowInit a => a Int Int
d = [| [arrow|
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