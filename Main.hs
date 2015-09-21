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
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
module Main where

import           Prelude hiding (id,(.),fst,snd)
import           Examples
import           Control.Arrow.CCA.Free
import Language.Haskell.Meta.Utils
import Language.Haskell.TH
import Language.Haskell.TH.Utilities
import Language.Haskell.TH.Syntax
import Control.Category
import Control.Categorical.Bifunctor.Rules
import Control.Categorical.Bifunctor
import Control.Applicative
import qualified Language.Haskell.Exts as E
import Data.Data
import qualified Control.Lens as L
import Data.Typeable
import Control.Arrow(arr)
import Data.Generics
import Control.Arrow.CCA.NoQ
import Control.Arrow.CCA.Rules
import Control.Category.Structural (Contract,(&&&),fst,snd,Weaken)
import Control.Arrow
import Control.Category.Free
import Control.Category.Rules
import Data.Maybe
deriving instance Show NameFlavour
deriving instance Show NameSpace
p :: (Arrow a,ArrowCCA a,Contract (,) a,Weaken (,) a) => a (b,c) (b,c)
p = [catCCA|
    proc (n,m) -> do
        id -< (n,m)
    |]

m :: FreeCategory (ASyn m) a a
m = s >>> s >>> id >>> id
s = FreeCategoryBaseOp (AExp Control.Arrow.CCA.Free.Swap)
undo :: Category cat => FreeCategory cat a b -> cat a b
undo (FreeCategoryBaseOp c) = c
undo (CategoryOp Control.Category.Free.Id) = id
undo (CategoryOp ((undo -> a) Control.Category.Free.:>>> (undo -> b))) = a >>> b
main :: IO ()
main = do
    --print $ [| fst >>> arr id >>> arr (+1) |] >>= L.rewriteM reifyLaws
    --print $ [| id >>> id |] >>= L.rewriteM reifyLaws
    --print $ [| first id >>> id >>> id |] >>= L.rewriteM reifyLaws
    printCCA p
    printCCA $ undo m
    printCCA $ undo $ rewrite (removeId) m
    --printCCA line4
    {-
    printCCA line1
    printCCA line2
    printCCA line3
    ---}
    --printCCA line4
    --print "Just proc-do desugar:"
    --printCCA example4b
    --print "CCA optimized:"

    --printCCA ( $(norm example4b))
    --print "Just proc-do desugar:"
    
    --print "CCA optimized:"
    --printCCA ( $(norm line1))
    --putStrLn ""
    --print "Just proc-do desugar:"
    --printCCA line2
    --print "CCA optimized:"
    --printCCA ($(norm line2))
    --print "Autos running in parallel"
    --let a = $(norm line2) :: AutoXIO (String,String) Int
    --    b = runAutoIO_ a
    --b ("http://www.google.com","http://www.cnn.com") >>= print . show
    --(runKleisli . runPKleisli) banana ("http://www.google.com","http://www.cnn.com") >>= print . show
    --(runKleisli . runPKleisli) example2 ("http://www.google.com","http://www.cnn.com") >>= print . show
    --print "hi"
