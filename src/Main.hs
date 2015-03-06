{-# LANGUAGE QuasiQuotes #-}
module Main where

import Control.Category
import Prelude hiding (id,(.))
import Control.Arrow
import Control.Arrow.Init.Optimize.TH
import Language.Haskell.TH (runQ)
import Examples

runCCNF :: e -> ((b, e) -> (c, e)) -> [b] -> [c]
runCCNF i f = g i
        where
            g _ [] = []
            g j (x:xs) = let (y, j') = f (x, j)
                            in y : g j' xs

nth' :: Int -> (b, ((), b) -> (a, b)) -> a
nth' n (i, f) = aux n i
  where
    aux m j = x `seq` if m == 0 then x else aux (m-1) j'
      where (x, j') = f ((), j)

runIt :: t -> (b, ((), b) -> (a, b)) -> a
runIt _ = nth' 0

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
---}
main :: IO ()
main = do
    print $ nth' 2 exampleOpt
    print $ complexA 2
    {-}
    runQ [arrow|
        proc n -> do
        Just a  <- arr (\x -> Just x) -< n
        rec
                e <- arr id -< a + n
                f <- arr id -< a - n
                g <- arr id -< a * n
                _ <- arr id -< e
        returnA -< e+1
            |]
    --}
    print "Optimizer complete"

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