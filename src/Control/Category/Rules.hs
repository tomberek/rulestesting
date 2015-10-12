{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE LambdaCase #-}
module Control.Category.Rules where
import Language.Haskell.TH.Utilities

import Control.Arrow
import Control.Category
import Prelude hiding (id,(.),fst,snd)
--import Control.Arrow.TH (ASyn)

import Debug.Trace
import Control.Category.Free

category_ruleset :: [RuleE]
category_ruleset = [category_id,category_id_comp,category_rightAssoc]

category_ruleset' :: [RuleE]
category_ruleset' = [category_id,category_id_comp,category_leftAssoc]


class Trans2' t k where
     drop2 :: t k a b -> k a b

instance Category cat => Trans2' FreeCategory cat where
    drop2 (FreeCategoryBaseOp a) = a
    drop2 (CategoryOp Id) = id
    drop2 (CategoryOp (a :>>> b)) = drop2 a >>> drop2 b

category_id :: RuleE
category_id [rule| arr id |]             = into [| id |]
category_id [rule| arr (\n -> m) |]  | m_ == n_            = into [| id |]
                              | otherwise = nothing
category_id [rule| \n -> m |] | m_ == n_ = into [| id |]
                              | otherwise = nothing
category_id [rule| returnA |]            = into [| id |]
category_id [rule| diag >>> fst |]       = into [| id |] --cartesian
category_id [rule| diag >>> snd |]       = into [| id |]
category_id [rule| swap >>> swap |] = into [| id |]
category_id a = return Nothing

category_id_comp :: RuleE
category_id_comp [rule| f >>> id |] = into [| $f |]
category_id_comp [rule| id >>> f |] = into [| $f |]
category_id_comp [rule| (id) |] = into [| id |]
category_id_comp a = return Nothing

category_leftAssoc :: RuleE
category_leftAssoc [rule| (f >>> i) >>> (g >>> h) |] = into [| ($f >>> ($i >>> $g)) >>> $h |]
category_leftAssoc [rule| (f >>> g) >>> h |] = into [| $f >>> ($g >>> $h) |]
category_leftAssoc a = return Nothing

category_rightAssoc :: RuleE
category_rightAssoc [rule| (f >>> i) >>> (g >>> h) |] = into [| $f >>> (($i >>> $g) >>> $h) |]
category_rightAssoc [rule| f >>> (g >>> h) |] = into [| ($f >>> $g) >>> $h |]
category_rightAssoc a = return Nothing
{-
--{-# RULES "arr id" forall n (m :: a->a). arr' n m = trace "fired arr id" id #-}
{-# RULES "arr id" forall n (m ::forall a b. (a,b)->(a,b)). arr' n m = trace "fired arr id" id #-}
{-# RULES "arr id" forall n. arr' n (\(a,b) -> (a,b)) = trace "fired arr2 id" id #-}
{-# RULES "arr id" arr (\(a,b) -> (a,b)) = trace "fired arr2 id" id #-}
{-# RULES "id >>> id" id >>> id = trace "fired id-id" id #-}
{-# RULES "id >>> (id >>> id) " id >>> (id >>> id) = trace "fired id-id-id" id #-}
{-# RULES "id >>> f" forall f. id >>> f = trace "fired id2" f #-}
{-# RULES "f >>> id" forall f. f >>> id = trace "fired id3" f #-}
{-# RULES "fst" forall n (m :: (a,b)->a). arr' n m = trace "fired fst" fst #-}
{-# RULES "snd" forall n (m :: (b,a)->a). arr' n m = trace "fired snd" snd #-}
{-# RULES "second" second id = trace "fired second" id #-}
-}