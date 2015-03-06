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

--a :: Int -> Int
(_,a) = [arrowExpOpt|
    proc n -> do
        rec b <- init (1::Int) -< c
            let c = b
        returnA -< c
        |]
---}

main :: IO ()
main = do
    --(runQ $ unTypeQ g) >>= print
    --print $ a 2
    runQ [arrowExp|
        proc n -> do
        rec d <- init 1 -< n
            let c = n
        returnA -< d+1
            |]
    {-
          rec let c = n+d
              d <- init 1 -< c
    -- -}
    print "hi"

draw x = putStrLn $ intercalate "\n\n" $ map show x