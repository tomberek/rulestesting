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
import Prelude hiding (id,(.),fst,snd)
import qualified Data.Constraint as C
import Control.Category.Rules (category_ruleset)
import Control.Categorical.Bifunctor.Rules (bifunctor_ruleset)
import Control.Arrow.CCA.Free
import Control.Arrow.CCA.NoQ

assoc_ruleset :: [RuleE]
assoc_ruleset = [assoc_ruleset_arr3,assoc_disassoc,assoc_ruleset_tuplize,assoc_ruleset_deArr]

assoc_ruleset_arr3 [rule| arr (\(a,(b,c)) -> ((x,y),z)) |]
    | a_ == x_ && b_ == y_ && c_ == z_ = into [| coassociate |]
    | a_ == y_ && b_ == x_ && c_ == z_ = into [| coassociate >>> first swap |]
    | a_ == x_ && b_ == z_ && c_ == y_ = into [| second swap >>> coassociate |]
    | otherwise = nothing
assoc_ruleset_arr3 _ = nothing


assoc_disassoc [rule| associate >>> cosassociate |] = into [|id|]
assoc_disassoc [rule| associate >>> snd |] = into [| first snd |]
assoc_disassoc [rule| associate >>> (snd >>> f) |] = into [| first snd >>> $f |]
assoc_disassoc [rule| coassociate >>> fst |] = into [| second fst |]
assoc_disassoc [rule| bimap associate id >>> associate >>> bimap id associate |] = into [| associate >>> associate |]
assoc_disassoc [rule| bimap id cosassociate >>> cosassociate >>> bimap associate id |] = into [| coassociate >>> coassociate |]
assoc_disassoc _ = nothing

assoc_ruleset_tuplize [rule| (\((a,b),(c,d)) -> (w,(x,(y,z)))) |]
    | a_ == w_ && b_ == x_ && c_ == y_ && d_ == z_ = into [| associate |]
    | otherwise = nothing
assoc_ruleset_tuplize _ = nothing

assoc_ruleset_deArr [rule| arr coassociate |] = into [| coassociate |]
assoc_ruleset_deArr [rule| arr associate |] = into [| associate |]
assoc_ruleset_deArr [rule| arr (associate >>> f) |] = into [| associate >>> arr $f |]
assoc_ruleset_deArr [rule| arr (coassociate >>> f) |] = into [| coassociate >>> arr $f |]
assoc_ruleset_deArr _ = nothing

assoc_left _ = return Nothing