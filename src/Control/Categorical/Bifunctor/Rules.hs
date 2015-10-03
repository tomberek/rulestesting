{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Control.Categorical.Bifunctor.Rules where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Utilities

import Control.Categorical.Bifunctor
import Control.Category
import Prelude hiding (id,(.))
import qualified Data.Constraint as C
import Control.Arrow.CCA.Free
import Control.Arrow (arr)
import Data.Proxy

bifunctor_ruleset :: [Exp -> Q (Maybe Exp)]
bifunctor_ruleset = [bifunctor_id,bifunctor_id_f,bifunctor_f_id,bifunctor_diag,bifunctor_arr,bifunctor_remove]

bifunctor_remove [rule| first f >>> second g |] = into [| $f *** $g |]
bifunctor_remove [rule| second g >>> first f |] = into [| $f *** $g |]
bifunctor_remove _ = nothing

bifunctor_id [rule| first id |]           = into [| id |]
bifunctor_id [rule| second id |]          = into [| id |]
bifunctor_id [rule| bimap id id |]        = into [| id |]
bifunctor_id [rule| id *** id |]          = into [| id |]
bifunctor_id _ = nothing

bifunctor_id_f :: RuleE
bifunctor_id_f [rule| bimap id f |] = into [| second $f |]
bifunctor_id_f [rule| id *** f |]   = into [| second $f |]
bifunctor_id_f [rule| fst &&& (snd >>> f) |] = into [| second $f |]
bifunctor_id_f _ = nothing

bifunctor_f_id :: RuleE
bifunctor_f_id [rule| bimap id f |] = into [| first $f |]
bifunctor_f_id [rule| id *** f |]   = into [| first $f |]
bifunctor_f_id [rule| (fst >>> f) &&& snd |] = into [| first $f |]
bifunctor_f_id _ = nothing

bifunctor_diag :: RuleE
bifunctor_diag [rule| (fst >>> f) &&& (snd >>> g) |] = into [| $f *** $g |]
bifunctor_diag _ = nothing

-- | Special rules for tuples in arr
bifunctor_arr :: RuleE
bifunctor_arr [rule| (\(x,y) -> (a,z)) |] | x_ == a_ = into [| second (\ $y -> $z) |]
                                          | y_ == z_ = into [| first (\ $x -> $a) |]
                                          | otherwise = nothing
bifunctor_arr [rule| arr (second f) |] = into [| second (arr $f)|]
bifunctor_arr [rule| arr (first f) |] = into [| first (arr $f)|]
bifunctor_arr [rule| arr (second f >>> g) |] = into [| second (arr $f) >>> arr $g |]
bifunctor_arr [rule| arr (first f >>> g) |] = into [| first (arr $f) >>> arr $g |]
bifunctor_arr _ = nothing
