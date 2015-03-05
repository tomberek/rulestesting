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
import Control.Arrow
import Control.CCA.CCNF
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

--optimized :: Int -> Int
--(a,optimized) = $(normOpt h)

out :: ASyn Int Int
out = $(norm h)

boring :: ASyn Int Int
boring = h
--}
main :: IO ()
main = do
    --(runQ $ unTypeQ g) >>= print
    runQ [arrowExp|
        proc n -> do
        Just a  <- arr (+1) >>> arr (\x -> Just x) -< n
        let c = a+a
            d = 0
        b <- arr (*10) -< a +5
        returnA -< n+1
            |]
    print "hi"

draw x = putStrLn $ intercalate "\n\n" $ map show x