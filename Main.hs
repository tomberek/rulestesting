{-# LANGUAGE QuasiQuotes     #-}
{-# LANGUAGE TemplateHaskell #-}
module Main where

import           Control.Category
import           Prelude                     hiding (id, (.))

--import           Auto
import           Control.Arrow
import           Control.Arrow.Init
import           Control.Arrow.Init.Optimize
import           Control.Arrow.TH
import           Examples
--import qualified Arrow as A

main :: IO ()
main = do
    {-
    let a =(example1 :: ASyn m Int Int)
    let b = $(norm example1)
    let (AExp c) = $(norm example1 >>= arrFixer)
    printCCA a
    print $ b 3
    print $(pprNorm example1)
    print c
    ---}
    printCCA line2
    printCCA $(normFixed line2)
    --let a = $(norm line2)
    let (_,b) = $(normOpt line2) :: ( (), PKleisli (String,String) Int)
    print $(pprNorm line2)
    --runAutoIO_ a ("http://www.google.com","http://www.cnn.com") >>= print . show
    (runKleisli . runPKleisli) b ("http://www.google.com","http://www.cnn.com") >>= print . show
    print "hi"

{-}
exampleOpt :: (Int, ((), Int) -> (Int, Int))
exampleOpt = [arrowOpt|
    proc () -> do
        rec a <- init (1::Int) -< b *10
            b <- arr (+4) -< a
        returnA -< a
        |]
complexA :: Int -> (Int,Int)
(_,complexA) = [arrowOpt|
    proc n -> do
        a <- arr (+5) -< n - (4::Int)
        c <- arr (*10) -< a +n
        d <- arr (+1) >>> arr (+43) -< a + c
        returnA -< (c,a)
        |]
complexB :: Int -> (Int,Int)
complexB = proc n -> do
    a <- arr (+5) -< n - (4::Int)
    c <- arr (*10) -< a +n
    d <- arr (+1) >>> arr (+43) -< a + c
    returnA -< (c,a)

newtype SF a b = SF { unSF :: a -> (b, SF a b) }
instance Category SF where
    id = SF (\a -> (a,id))
    b . a =  SF (h a b)
        where h f g x = let (y, f') = unSF f x
                            (z, g') = unSF g y
                          in (z, SF (h f' g'))
instance Arrow SF where
    arr f = SF h
        where h x = (f x, SF h)
    first a = SF (h a)
        where h f (x, z) = let (y, f') = unSF f x
                                in ((y, z), SF (h f'))
instance ArrowLoop SF where
    loop a = SF (h a)
        where h f x = let ((y, z), f') = unSF f (x, z)
                            in (y, SF (h f'))
instance ArrowInit SF where
    init a = SF (h a)
        where h i x = (i, SF (h x))

runSF :: SF a b -> [a] -> [b]
runSF f (x:xs) = let (y, f') = unSF f x
                           in y: runSF f' xs
runSF _ [] = []
---}
---}
---}
