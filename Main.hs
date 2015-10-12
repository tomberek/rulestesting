{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE QuasiQuotes     #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
module Main where

import           Prelude hiding (id,(.),fst,snd)
import           Examples
import           Control.Arrow.CCA.Free
import           Control.Arrow.CCA
import Control.Arrow.CCA.Rules
import Control.Category.Structural
import Data.Functor.Identity
import Control.Arrow(Kleisli(..))
{-
p :: (Arrow a,ArrowCCA a,Contract (,) a,Weaken (,) a) => a (b,c) (b,c)
p = [catCCA|
    proc (n,m) -> do
        id -< (n,m)
    |]
-}

--t :: Weaken (,) a => a (Int,Int) Int
--t = $(toExpCCA (line3 :: FreeCCA Identity () (,) (->) (Int,Int) Int))
t2 :: (IO ~ M a) => a (String,String) Int
t2 = $(toExpCCA (line7 :: FreeCCA IO () (,) (Kleisli IO) (String,String) Int))

main :: IO ()
main = do
    print "hi"
    printExp line3
    --printExp t
    printExp (line7 :: FreeCCA IO () (,) (Kleisli IO) (String,String) Int)
    --print "Autos running in parallel"
    --let a = $(norm line2) :: AutoXIO (String,String) Int
    --    b = runAutoIO_ a
    --b ("http://www.google.com","http://www.cnn.com") >>= print . show
    --(runKleisli . runPKleisli) banana ("http://www.google.com","http://www.cnn.com") >>= print . show
    --(runKleisli . runPKleisli) example2 ("http://www.google.com","http://www.cnn.com") >>= print . show
    --print "hi"
