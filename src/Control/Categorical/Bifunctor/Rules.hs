{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
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
import Language.Haskell.TH.Utilities

import Control.Categorical.Bifunctor
import Control.Categorical.Bifunctor.Free
import Control.Category.Free
import Control.Category
import Control.Category.Rules
import Prelude hiding (id,(.))
import Control.Arrow (arr)
import Data.Generics.Multiplate
import Control.Applicative

(...) :: Category k => k b c -> (a -> k d b) -> a -> k d c
(...) = (.).(.)

data BiPlate f = BiPlate {
    biid ::forall p cat a. f (FreeBifunctor p cat a a),
    bicomp ::forall p cat a b c. FreeBifunctor p cat a b -> FreeBifunctor p cat b c -> f (FreeBifunctor p cat a c),
    bibase ::forall p cat a b. cat a b -> f (FreeBifunctor p cat a b),
    bifunc ::forall p cat a b c d. FreeBifunctor p cat a b -> FreeBifunctor p cat c d -> f (FreeBifunctor p cat (p a c) (p b d))
    }

expr :: BiPlate f -> (FreeBifunctor p cat a b) -> f (FreeBifunctor p cat a b)
expr plate (FreeBifunctorCategoryOp Id) = biid plate
expr plate (FreeBifunctorCategoryOp (a :>>> b)) = bicomp plate a b
expr plate (FreeBifunctorBaseOp a) = bibase plate a
expr plate (BifunctorOp (a :*** b)) = bifunc plate a b

instance Multiplate BiPlate where
    multiplate plate = BiPlate
        (pure $ FreeBifunctorCategoryOp Id)
        (\a b -> (FreeBifunctorCategoryOp ... (:>>>)) <$> expr plate a <*> expr plate b)
        (\a -> pure $ FreeBifunctorBaseOp a)
        (\a b -> (BifunctorOp ... (:***)) <$> expr plate a <*> expr plate b)
    mkPlate build = BiPlate
        (build expr (FreeBifunctorCategoryOp Id))
        (\a b -> build expr (FreeBifunctorCategoryOp (a :>>> b)))
        (\a -> build expr (FreeBifunctorBaseOp a))
        (\a b -> build expr (BifunctorOp (a :*** b)))

bifunctor_ruleset :: [Exp -> Q (Maybe Exp)]
bifunctor_ruleset = [bifunctor_id,bifunctor_id_f,bifunctor_f_id,bifunctor_diag,bifunctor_arr,bifunctor_remove]

bifunctor_remove :: RuleE
bifunctor_remove [rule| first f >>> second g |] = into [| $f *** $g |]
bifunctor_remove [rule| second g >>> first f |] = into [| $f *** $g |]
bifunctor_remove _ = nothing

bifunctor_id :: RuleE
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
bifunctor_f_id [rule| f *** id |]   = into [| first $f |]
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

instance (PFunctor p cat) => Trans2' (FreePFunctor p) cat where
    drop2 (FreePFunctorBaseOp a) = a
    drop2 (FreePFunctorCategoryOp Id) = id
    drop2 (FreePFunctorCategoryOp (a :>>> b)) = drop2 a >>> drop2 b
    drop2 (PFunctorOp (First a)) = first $ drop2 a
instance (QFunctor p cat) => Trans2' (FreeQFunctor p) cat where
    drop2 (FreeQFunctorBaseOp a) = a
    drop2 (FreeQFunctorCategoryOp Id) = id
    drop2 (FreeQFunctorCategoryOp (a :>>> b)) = drop2 a >>> drop2 b
    drop2 (QFunctorOp (Second a)) = second $ drop2 a
instance (Bifunctor p cat) => Trans2' (FreeBifunctor p) cat where
    drop2 (FreeBifunctorBaseOp a) = a
    drop2 (FreeBifunctorCategoryOp Id) = id
    drop2 (FreeBifunctorCategoryOp (a :>>> b)) = drop2 a >>> drop2 b
    drop2 (BifunctorOp (a :*** b)) = drop2 a *** drop2 b
