{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
module Control.Category.Structural.Rules where

import Language.Haskell.TH
import Language.Haskell.TH.Quote
import Language.Haskell.TH.Utilities

import Control.Arrow (arr)
import Control.Category.Structural
import Control.Category.Structural.Free
import Control.Category
import Prelude hiding (id,(.),fst,snd)
import Control.Category.Rules
import Control.Category.Free
import Control.Categorical.Bifunctor.Rules
import Control.Categorical.Bifunctor.Free
import Control.Categorical.Bifunctor
import Control.Category.Associative.Rules
import Control.Arrow.CCA.Free(category)

structural :: QuasiQuoter
structural = category $ [ bifunctor_ruleset ++ assoc_ruleset  ++ struct_ruleset ++ category_ruleset',
                           category_ruleset' ++ bifunctor_ruleset  ++ assoc_ruleset ++ struct_ruleset,
                              category_ruleset ++ bifunctor_ruleset ++ assoc_ruleset ++ struct_ruleset]

struct_ruleset :: [RuleE]
struct_ruleset =[struct_rules,struct_rules_bi,struct_weak,struct_rules_trav,struct_rules_rare]

struct_rules :: RuleE
struct_rules [rule| arr snd |] = into [| snd |]
struct_rules [rule| arr fst |] = into [| fst |]
struct_rules [rule| arr (snd >>> f) |] = into [| snd >>> arr $f |]
struct_rules [rule| arr (fst >>> f) |] = into [| fst >>> arr $f |]
struct_rules [rule| (\(x,y) -> z) |] | x_ == z_ = into [| fst |]
                                     | y_ == z_ = into [| snd |]
                                     | case x_ of
                                         VarE a -> not $ nameOccursIn a z_
                                         _ -> False
                                         = into [| (snd >>> (\ $y -> $z )) |]
                                     | case y_ of
                                         VarE a -> not $ nameOccursIn a z_
                                         _ -> False
                                         = into [| (fst >>> (\ $x -> $z )) |]
                                     | otherwise = nothing
struct_rules _ = nothing

struct_weak :: RuleE
struct_weak [rule| (\((a,b),(c,d)) -> (x,y)) |] | a_ == x_ && c_ == y_ = into [| fst *** fst |]
                                                | a_ == x_ && d_ == y_ = into [| fst *** snd |]
                                                | b_ == x_ && c_ == y_ = into [| snd *** fst |]
                                                | b_ == x_ && d_ == y_ = into [| snd *** snd |]
                                                | otherwise = return Nothing
struct_weak [rule| (\(x,y) -> (a,z)) |] | x_ == z_ = into [| swap >>> first (\ $y -> $a) |]
                                        | y_ == a_ = into [| swap >>> second (\ $x -> $z) |]
                                        | otherwise = return Nothing
struct_weak [rule| arr swap |] = into [| swap |]
struct_weak [rule| (f *** g) >>> snd |] = into [| snd >>> $g |]
struct_weak [rule| (f *** g) >>> fst |] = into [| fst >>> $f |]
struct_weak _ = return Nothing

struct_rules_bi :: RuleE
struct_rules_bi [rule| (fst >>> f) &&& (snd >>> g) |] = into [| $f *** $g |]
struct_rules_bi [rule| (snd >>> f) &&& (fst >>> g) |] = into [| swap >>> ($f *** $g) |]
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
struct_rules_bi [rule| swap >>> first f |] = into [| second $f >>> swap |] -- bubble all swaps to the right
struct_rules_bi [rule| swap >>> second f |] = into [| first $f >>> swap |] -- bubble all swaps to the right
struct_rules_bi [rule| swap >>> (f *** g) |] = into [| ($g *** $f) >>> swap |] -- bubble all swaps to the right
struct_rules_bi [rule| first f >>> fst |] = into [| fst >>> $f |] -- bubble all fst to the left
struct_rules_bi [rule| second f >>> snd |] = into [| snd >>> $f |] -- bubble all snd to the left
struct_rules_bi [rule| first f >>> snd |] = into [| snd |]
struct_rules_bi [rule| second f >>> fst |] = into [| fst |]

struct_rules_bi [rule| swap >>> fst |] = into [| snd |]
struct_rules_bi [rule| swap >>> snd |] = into [| fst |]
struct_rules_bi [rule| diag >>> swap |] = into [| diag |]
struct_rules_bi [rule| diag >>> (swap >>> f) |] = into [| diag >>> $f |]
struct_rules_bi _ = return Nothing


struct_rules_trav :: RuleE
struct_rules_trav [rule| (f &&& g) >>> (h *** i) |] = into [| ($f >>> $h) &&& ($g >>> $i) |]
struct_rules_trav _ = nothing

-- | Perhaps do right assoc, then right swap?, this seems like too much "special case"
struct_rules_rare :: RuleE
struct_rules_rare [rule| swap >>> arr (\(a,b) -> c) |] = into [| arr (\($b,$a) -> $c) |]
struct_rules_rare _ = return Nothing

instance (Weaken p cat) => Trans2' (FreeWeaken p) cat where
    drop2 (FreeWeakenBaseOp a) = a
    drop2 (FreeWeakenCategoryOp Id) = id
    drop2 (FreeWeakenCategoryOp (a :>>> b)) = drop2 a >>> drop2 b
    drop2 (FreeWeakenBifunctorOp (a :*** b)) = drop2 a *** drop2 b
    drop2 (WeakenOp Fst) = fst
    drop2 (WeakenOp Snd) = snd
instance (Contract p cat) => Trans2' (FreeContract p) cat where
    drop2 (FreeContractBaseOp a) = a
    drop2 (FreeContractCategoryOp Id) = id
    drop2 (FreeContractCategoryOp (a :>>> b)) = drop2 a >>> drop2 b
    drop2 (FreeContractBifunctorOp (a :*** b)) = drop2 a *** drop2 b
    drop2 (ContractOp Diag) = diag
instance (Symmetric p cat) => Trans2' (FreeSymmetric p) cat where
    drop2 (FreeSymmetricBaseOp a) = a
    drop2 (FreeSymmetricCategoryOp Id) = id
    drop2 (FreeSymmetricCategoryOp (a :>>> b)) = drop2 a >>> drop2 b
    drop2 (FreeSymmetricBifunctorOp (a :*** b)) = drop2 a *** drop2 b
    drop2 (SymmetricOp Swap) = swap
{-


-}

