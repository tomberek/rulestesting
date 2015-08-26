{-# LANGUAGE QuasiQuotes     #-}
{-# LANGUAGE TypeFamilies    #-}
module Examples where
import           Control.Arrow.CCA.Optimize
import           Control.Arrow.TH
import           Control.Arrow
import           Control.Concurrent          (threadDelay)
import Control.Concurrent.Async
import           Data.Time
import           Network.HTTP
import Prelude hiding (id,(.))
{-
line1 :: (M a ~ IO,ArrowCCA a) => a (String, String) ()
line1 = [arrow| proc (n,g) -> do
    a <- getURLSum -< n
    d <- getURLSum -< g
    b <- arr length -< n
    c <- arrM (\input -> do
               print input
               print ":"
               read <$> getLine) -< n
    _ <- arrM print -< a + c + d
    returnA -< ()
    |]
---}

processURL :: String -> IO String
processURL a = do
    getCurrentTime >>= print
    threadDelay 1000000
    response <- simpleHTTP (getRequest a)
    getResponseBody response

getURLSum :: (M a ~ IO,ArrowCCA a) => a String Int
getURLSum = [arrow| (arrM processURL) >>> (arr length) |]

line2 :: (M a ~ IO, ArrowCCA a) => a (String,String) Int
line2 = [arrow|
    proc (x,y) -> do
        a <- getURLSum -< y
        b <- getURLSum -< x
        returnA -< a+b
    |]
line3 :: ArrowCCA a => a (b,c) (c,c)
line3 = [arrow|
    proc n -> do
    a <- arr fst -< n
    b <- arr snd -< n
    c <- id -< (b,b)
    d <- id -< (c,a)
    e <- arr fst . arr fst -< d
    returnA -< (b,e)
    |]

{- no implemented yet
example1 :: ArrowCCA a => a Int Int
example1 = [arrow|
    proc n -> do
        a  <- arr (\x -> x) -< (n::Int)
        rec
            e <- arr (+1) -< a + (1::Int)
        returnA -< a
    |]
-}


example4 :: ArrowCCA a => a Int Int
example4 = [arrow|
     proc n -> do
        a <- arr (+1) -< n
        returnA -< n
        _ <- arr (*2) -< n+1
        d <- arr (*2) -< a*1
        returnA -< n
            |]
example4b :: ArrowCCA a => a Int Int
example4b = [arrow|
     proc n -> do
        d <- arr (uncurry (+)) -< (n,n)
        arr (uncurry (-)) -< (n,d)
            |]
example2 :: ArrowCCA a => a Int Int
example2 = [arrow|
    proc n -> do
        b <-  arr (+1) -< n+2*3
        e <-  arr (+2) -< n
        c <-  arr (+3) -< b
        d <-  arr (uncurry (+)) -< (c,e)
        arr (uncurry (-)) -< (n,d)
            |]
---}
---}

{- no implemented yet
example1 :: ArrowInit a => a Int Int
example1 = [arrow|
    proc n -> do
        a  <- arr (\x -> x) -< (n::Int)
        rec
            e <- arr (+1) -< a + (1::Int)
        returnA -< a
    |]


{-
i :: ArrowCCA a => a Int Int
i = [arrow|
    proc n -> do
        x <- arr id -< n
        y <- arr (+1) -< x
        let z = x+y
        returnA -< z
        |]

---}
---}
