{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE Arrows #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Examples 
     where
import Parser
import Control.Arrow hiding (arr)
import qualified Control.Arrow as A
import Control.CCA.Types
import Debug.Trace
import qualified Control.CCA as C

arr :: Arrow a => (b->c) -> a b c
arr = A.arr . trace "hi" --local capture of arr!

addN :: ArrowInit a => a Int Int
addN = $(C.arr [| (+3) |] )

cJust :: ArrowInit a => a Int (Maybe Int)
cJust = $(C.arr [| \x -> Just x |])

idA :: ArrowInit a => a b b
idA = $(C.arr [| id |] )

h :: ArrowInit a => a Int Int
h = [arrow|proc n -> addN -< n+2 |]

f :: ArrowInit a => a Int Int
f = [arrow|
    proc n -> do
        Just a  <- addN >>> cJust -< n
        _ <- addN -< n+1
        idA -< a+1
    |]
e :: ArrowInit a => a Int Int
e = [arrow|
    proc n -> do
        returnA -< 10*n
        returnA -< 20*n
    |]
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