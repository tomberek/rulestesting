{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
module Control.Category.Associative.Rules where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Utilities

import Control.Arrow
import Control.Category.Associative
import Control.Category.Structural
import Control.Category
import Prelude hiding (id,(.))
import qualified Data.Constraint as C
import Control.Category.Rules (category_ruleset)
import Control.Categorical.Bifunctor.Rules (bifunctor_ruleset)
import Control.Arrow.CCA.Free
import Control.Arrow.CCA.NoQ

assoc_ruleset :: [RuleE]
assoc_ruleset = [assoc_left]

assoc_left _ = return Nothing