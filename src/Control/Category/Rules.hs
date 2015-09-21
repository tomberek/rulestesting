{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
module Control.Category.Rules where
import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Utilities

import Control.Arrow
import Control.Category.Associative
import Control.Category.Structural
import Control.Category
import Prelude hiding (id,(.),fst,snd)
import qualified Data.Constraint as C
--import Control.Arrow.TH (ASyn)
import Data.Data
import Debug.Trace
import Control.Arrow.CCA.NoQ
import Control.Category.Free
--import Control.Arrow.CCA.Free
import Control.Applicative
import Control.Monad.Identity
category_ruleset :: [Exp -> Q (Maybe Exp)]
category_ruleset = [] --category_id,category_id_comp,category_leftAssoc]

instance Compos (FreeCategory) where
    compos f t = case t of
        CategoryOp Id -> pure id
        CategoryOp (a :>>> b) -> CategoryOp <$> (pure (:>>>) <*> f a <*> f b)
        _ -> pure t

rewrite :: Compos t => (forall (t :: (* -> * -> *) -> * -> * -> *) cat a b. t cat a b -> Maybe ( (t cat a b))) ->
           t cat a b -> t cat a b
rewrite f = composOp g
    where
        g :: forall (t :: (* -> * -> *) -> * -> * -> *) a b. (forall (cat :: * -> * -> *). Compos t => t cat a b -> t cat a b)
        g x = maybe x (rewrite f) (f x)

removeId :: FreeCategory cat a b -> Maybe (FreeCategory cat a b)
removeId t = case t of
    CategoryOp (CategoryOp Id :>>> b) -> Just b
    CategoryOp (b :>>> CategoryOp Id) -> Just b
    CategoryOp Id -> Nothing
    FreeCategoryBaseOp _ -> Nothing
    _ -> composM removeId t

class Compos t where
    compos :: Applicative f => (forall (cat :: * -> * -> *) a b. t cat a b -> f (t cat a b)) ->
        t cat a b -> f (t cat a b)
composOp :: Compos t => (forall cat a b. t cat a b -> t cat a b) -> t cat a b -> t cat a b
composOp f = runIdentity . compos (Identity . f)
composM :: (Compos t,Monad m) => (forall (cat :: * -> * -> *)  a b. t cat a b -> m (t cat a b)) ->
        t cat a b -> m (t cat a b)
composM f = unwrapMonad . compos (WrapMonad . f)
composAlt :: (Compos t,Alternative m,Monad m) => (forall (cat :: * -> * -> *)  a b. t cat a b -> m (t cat a b)) ->
          t cat a b -> m (t cat a b)
composAlt f = unwrapMonad . composM (WrapMonad . f)

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
category_id :: RuleE
--category_id [rule| arr (\n -> m) |] | m_ == n_ = into [| id |]
--category_id [rule| \n -> m |] | m_ == n_ = into [| id |]
category_id [rule| arr id |]             = into [| id |]
category_id [rule| returnA |]            = into [| id |]
category_id [rule| first id |]           = into [| id |]
category_id [rule| second id |]          = into [| id |]
category_id [rule| diag >>> fst |]       = into [| id |] --cartesian
category_id [rule| diag >>> snd |]       = into [| id |]
category_id [rule| bimap id id |] = into [| id |]
category_id [rule| id *** id |]   = into [| id |]
category_id [rule| bimap fst snd |] = into [| id |]
category_id [rule| fst *** snd |] = into [| id |]
category_id [rule| swap >>> swap |] = into [| id |]
category_id a = return Nothing

category_id_comp :: RuleE
category_id_comp [rule| f >>> id |] = into [| $f |]
category_id_comp [rule| id >>> f |] = into [| $f |]
category_id_comp a = return Nothing

category_leftAssoc :: RuleE
category_leftAssoc [rule| f >>> (g >>> h) |] = into [| ($f >>> $g) >>> $h |]
category_leftAssoc a = return Nothing