{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}
{- |
Module      :  Control.Arrow.CCA.Optimize
Description :  Optimize ArrowCCA Instances
Copyright   :  (c) 2015 Thomas Bereknyei
License     :  BSD3
Maintainer  :  Thomas Bereknyei <tomberek@gmail.com>
Stability   :  unstable
Portability :  GADTs,TemplateHaskell,MultiParamTypesClasses

Originally from CCA package: <https://hackage.haskell.org/package/CCA-0.1.5.2>
-}
module Control.Arrow.CCA.Optimize
    (norm, normOpt, fromAExp, normalize,normalizeTrace,
    runCCNF, nth', runIt,
    pprNorm, pprNormOpt, printCCA, ASyn(..),AExp(..),ArrowCCA(..),(.),id
    --cross, dup, swap, assoc, unassoc, juggle, trace, mirror, untag, tagT, untagT,
    --swapE, dupE
    ) where

import Control.Category.Associative
import Control.Category.Structural
import Control.Category.Monoidal
import Control.Category.Cartesian
import Control.Categorical.Bifunctor.Rules

import           Control.Category
import           Prelude             hiding (id, (.),fst,snd)
import           Control.Arrow hiding (first,second,(***),(&&&))
import qualified Control.Arrow as A
import           Control.Arrow.CCA
import           Control.Arrow.TH
import           Control.Monad(liftM)
import           Control.Applicative
import           Data.Char           (isAlpha)
import           Language.Haskell.TH
import           Language.Haskell.TH.Utilities
import           Data.Bitraversable
import           Control.Parallel
import qualified Control.Lens as L
import Control.Lens hiding (Bifunctor)
import qualified Debug.Trace
import Data.Data (Data(..))
import qualified Data.Generics       as G (everywhere, mkT)

