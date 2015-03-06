{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TemplateHaskell #-}
module Main where

import Control.Category
import Prelude hiding (id,(.))

import Data.List (intercalate)
import Examples
import Parser
import Control.CCA.CCNF
import Control.CCA.Types
--import Control.CCA
import Debug.Trace
import Control.Arrow
import Language.Haskell.TH (runQ)

--g =  [||  [arrow| proc n -> arr (+1) -< n |] :: Int -> Int ||]

runCCNF :: e -> ((b, e) -> (c, e)) -> [b] -> [c]
runCCNF i f = g i
        where g i (x:xs) = let (y, i') = f (x, i)
                            in y : g i' xs

nth' :: Int -> (b, ((), b) -> (a, b)) -> a
nth' n (i, f) = aux n i
  where
    aux n i = x `seq` if n == 0 then x else aux (n-1) i'
      where (x, i') = f ((), i)
runIt x = nth' 0

--z :: () -> Int
--z :: SF () Int
z = [arrowExpOpt|
    proc () -> do
        rec a <- init (1::Int) -< b *10
            b <- arr (+4) -< a
        returnA -< a
        |]
complexA :: Int -> (Int,Int)
(_,complexA) = [arrowExpOpt|
    proc n -> do
        a <- arr (+5) -< n - (4::Int)
        c <- arr (*10) -< a +n
        d <- arr (+1) -< a + c
        returnA -< (c,a)
        |]
---}

main :: IO ()
main = do
    --(runQ $ unTypeQ g) >>= print
    print $ nth' 2 z
    print $ complexA 2
    {-
    runQ [arrowExp|
        proc () -> do
        rec b <- init (1::Int) -< a+1
            a <- arr (+4) -< b
        returnA -< b
            |]
    --}
    print "hii"
    print "hi"

draw x = putStrLn $ intercalate "\n\n" $ map show x
newtype SF a b = SF { unSF :: a -> (b, SF a b) }
instance Category SF where
    id = SF (\a -> (a,id))
    (.) = flip (>:>)
f >:> g = SF (h f g)
        where h f g x = let (y, f') = unSF f x
                            (z, g') = unSF g y
                          in (z, SF (h f' g'))
instance Arrow SF where
    arr f = SF h
        where h x = (f x, SF h)
    first f = SF (h f)
        where h f (x, z) = let (y, f') = unSF f x
                                in ((y, z), SF (h f'))
instance ArrowLoop SF where
    loop f = SF (h f)
        where h f x = let ((y, z), f') = unSF f (x, z)
                            in (y, SF (h f'))
instance ArrowInit SF where
    init i = SF (h i)
        where h i x = (i, SF (h x))

runSF :: SF a b -> [a] -> [b]
runSF f = g f
    where g f (x:xs) = let (y, f') = unSF f x
                           in y: g f' xs