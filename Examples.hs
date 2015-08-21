{-# LANGUAGE QuasiQuotes     #-}
{-# LANGUAGE TypeFamilies    #-}
module Examples where
import           Control.Arrow.Init.Optimize
import           Control.Arrow.TH


import           Control.Arrow

{-
import           Control.Concurrent          (threadDelay)
import           Data.Time
import           Network.HTTP
line1 :: (M a ~ IO,ArrowInit a) => a (String, String) ()
line1 = [arrowInit| proc (n,g) -> do
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

processURL :: String -> IO String
processURL a = do
    getCurrentTime >>= print
    threadDelay 1000000
    response <- simpleHTTP (getRequest a)
    getResponseBody response

getURLSum :: (M a ~ IO,ArrowInit a) => a String Int
getURLSum = [arrowInit| (arrM processURL) >>> (arr length) |]

line2 :: (M a ~ IO, ArrowInit a) => a (String,String) Int
line2 = [arrowInit|
    proc (x,y) -> do
    a <- getURLSum -< x
    b <- getURLSum -< y
    returnA -< a+b
    |]
line3 :: (M a ~ IO, ArrowInit a) => a (String,String) Int
line3 = [arrowInit|
    proc a -> do
    (c,d) <- getURLSum *** getURLSum -< a
    returnA -< c+d
    |]

example1 :: ArrowInit a => a Int Int
example1 = [arrowInit|
    proc n -> do
        a  <- arr (\x -> x) -< (n::Int)
        rec
            e <- arr (+1) -< a + (1::Int)
        returnA -< a
    |]


---}

example4 :: ArrowInit a => a Int Int
example4 = [arrow|
     proc n -> do
        a <- arr (+1) -< n
        returnA -< n
        _ <- arr (*2) -< n+1
        d <- arr (*2) -< a*1
        returnA -< n
            |]
example4b :: ArrowInit a => a Int Int
example4b = [arrow|
     proc n -> do
        a <- arr (+1) -< n
        () <- returnA -< n
        _ <- arr (*2) -< n+1
        d <- arr (*2) -< a*1
        returnA -< n+1
            |]

example2 :: ArrowInit a => a Int Int
example2 = [arrow|
    proc n -> do
        b <-  arr (+1) -< n
        e <-  arr (+2) -< n
        c <-  arr (+3) -< b
        d <-  arr (uncurry (+)) -< (c,e)
        arr (uncurry (-)) -< (d,n)
            |]

{-
i :: Int -> Int
i = [arrow|
    proc n -> do
        x <- arr id -< n + n
        y <- arr (+1) -< x
        let z = x + y
        returnA -< z
        |]

---}
---}
