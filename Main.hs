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
import           Control.Categorical.Bifunctor
import           Control.Category
import Control.Arrow.CCA.Rules
import Control.Category.Structural
import Data.Functor.Identity
import Control.Arrow(Kleisli(..))
import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Control.Monad
{-
p :: (Arrow a,ArrowCCA a,Contract (,) a,Weaken (,) a) => a (b,c) (b,c)
p = [catCCA|
    proc (n,m) -> do
        id -< (n,m)
    |]
-}

t :: Weaken (,) a => a (Int,Int) Int
t = $(toExpCCA (line3 :: FreeCCA Identity () (,) (->) (Int,Int) Int))
t2 :: (IO ~ M a,ArrowCCA a,Bifunctor (,) a) => a (String,String) Int
t2 = $(toExpCCA (line7 :: FreeCCA IO () (,) (Kleisli IO) (String,String) Int))

--t3 :: ExpQ
t3 :: (ArrowCCA a,Contract (,) a) => a Int Int
t3 = $(toExpCCA (example2 :: (IO ~ M (Kleisli IO) ) => FreeCCA IO () (,) (Kleisli IO) Int Int))

main :: IO ()
main = do
    printExp line3
    printExp t
    printExp (line7 :: FreeCCA IO () (,) (Kleisli IO) (String,String) Int)
    printExp (t2 :: FreeCCA IO () (,) (Kleisli IO) (String,String) Int)

    let g = (example2 :: FreeCCA IO () (,) (Kleisli IO) Int Int)
    printExp (example2 :: FreeCCA IO () (,) (Kleisli IO) Int Int)
    printExp (t3 :: FreeCCA IO () (,) (Kleisli IO) Int Int)
    print "hi"
    
    --print "Autos running in parallel"
    --let a = $(norm line2) :: AutoXIO (String,String) Int
    --    b = runAutoIO_ a
    --b ("http://www.google.com","http://www.cnn.com") >>= print . show
    --(runKleisli . runPKleisli) banana ("http://www.google.com","http://www.cnn.com") >>= print . show
    --(runKleisli . runPKleisli) example2 ("http://www.google.com","http://www.cnn.com") >>= print . show
    --print "hi"