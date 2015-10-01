{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
module Control.Category.Structural.Rules where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Utilities

import Control.Arrow hiding ((&&&))
import Control.Category.Associative
import Control.Category.Structural
import Control.Category
import Prelude hiding (id,(.),fst,snd)
import qualified Data.Constraint as C
import Control.Category.Rules (category_ruleset)
import Control.Categorical.Bifunctor.Rules (bifunctor_ruleset)
import Control.Arrow.CCA.Free
import Control.Arrow.CCA.NoQ
import Control.Applicative

struct_ruleset :: [RuleE]
struct_ruleset =[struct_rules,struct_rules_bi,struct_weak,struct_rules_rare]

struct_rules [rule| (\(x,y) -> z) |] | x_ == z_ = into [| fst |]
                                     | y_ == z_ = into [| snd |]
                                     | otherwise = return Nothing
struct_rules [rule| arr snd |] = into [| snd |]
struct_rules [rule| arr fst |] = into [| fst |]
struct_rules _ = return Nothing

struct_weak [rule| (\((a,b),(c,d)) -> (x,y)) |] | a_ == x_ && c_ == y_ = into [| fst *** fst |]
                                                | a_ == x_ && d_ == y_ = into [| fst *** snd |]
                                                | b_ == x_ && c_ == y_ = into [| snd *** fst |]
                                                | b_ == x_ && d_ == y_ = into [| snd *** snd |]
                                                | otherwise = return Nothing
struct_weak [rule| arr (\(x,y) -> (a,z)) |] | x_ == z_ = into [| swap >>> first (arr (\ $y -> $a)) |]
                                            | y_ == a_ = into [| swap >>> second (arr (\ $x -> $z)) |]
                                            | otherwise = return Nothing
struct_weak [rule| (f *** g) >>> snd |] = into [| snd >>> $g |]
struct_weak [rule| (f *** g) >>> fst |] = into [| fst >>> $f |]
struct_weak _ = return Nothing

struct_rules_bi [rule| (fst >>> f) &&& (snd >>> g) |] = into [| $f *** $g |]
struct_rules_bi [rule| (snd >>> f) &&& (fst >>> g) |] = into [| $g *** $f |]
struct_rules_bi [rule| fst &&& (snd >>> g) |] = into [| id *** $g |]
struct_rules_bi [rule| (fst >>> f) &&& snd |] = into [| $f *** id |]
struct_rules_bi [rule| snd &&& (fst >>> g) |] = into [| swap >>> (id *** $g) |]
struct_rules_bi [rule| (snd >>> f) &&& fst |] = into [| swap >>> ($f *** id) |]
struct_rules_bi [rule| (f &&& g) >>> fst |] = into [| $f |]
struct_rules_bi [rule| (f &&& g) >>> snd |] = into [| $g |]
struct_rules_bi [rule| diag >>> (f *** g) |] = into [| $f &&& $g |] -- TODO: is this sound?
struct_rules_bi [rule| fst &&& snd |] = into [| id |] -- or should this be `id *** id`
struct_rules_bi [rule| snd &&& fst |] = into [| swap |] -- or should this be `swap >>> id *** id`
struct_rules_bi [rule| id &&& id |] = into [| diag |]
struct_rules_bi [rule| f &&& id |] = into [| diag >>> first $f |]
struct_rules_bi [rule| id &&& g |] = into [| diag >>> second $g |]
struct_rules_bi [rule| (f &&& g) >>> swap |] = into [| $g &&& $f |]
struct_rules_bi [rule| (a >>> f) &&& (b >>> g) |] | a_ == b_ = into [| $a >>> ($f &&& $g) |] -- sound forall equalities?
                                                  | otherwise = return Nothing
struct_rules_bi [rule| a &&& (b >>> g) |] | a_ == b_ = into [| $a >>> (id &&& $g) |] -- sound forall equalities?
                                          | otherwise = return Nothing
struct_rules_bi [rule| (a >>> f) &&& b |] | a_ == b_ = into [| $a >>> ($f &&& id) |] -- sound forall equalities?
                                          | otherwise = return Nothing
struct_rules_bi [rule| diag >>> arr f |] = into [| arr ( $f . diag ) |] -- There are/should be no rules with diag on the right, this this is sound
struct_rules_bi [rule| diag >>> first f >>> swap |] = into [| diag >>> second $f |]
struct_rules_bi [rule| diag >>> second f >>> swap |] = into [| diag >>> first $f |]
{-
struct_rules_bi [rule| first f >>> swap |] = into [| swap >>> second $f |] -- bubble all swaps to the left
struct_rules_bi [rule| second f >>> swap |] = into [| swap >>> first $f |] -- bubble all swaps to the left
--}
struct_rules_bi [rule| swap >>> first f |] = into [| second $f >>> swap |] -- bubble all swaps to the right
struct_rules_bi [rule| swap >>> second f |] = into [| first $f >>> swap |] -- bubble all swaps to the right

struct_rules_bi [rule| diag >>> swap |] = into [| diag |]
struct_rules_bi [rule| diag >>> (swap >>> f) |] = into [| diag >>> $f |]
struct_rules_bi _ = return Nothing

-- | Perhaps do right assoc, then right swap?, this seems like too much "special case"
struct_rules_rare [rule| swap >>> arr (\(a,b) -> c) |] = into [| arr (\($b,$a) -> $c) |]
struct_rules_rare _ = return Nothing
{-


-}

