{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
module Control.Category.Monoidal.Rules where

import Prelude hiding (id,(.))
import Control.Category.Rules
import Control.Category.Monoidal.Free
import Control.Category.Monoidal
import Control.Category.Free
import Control.Category
import Control.Categorical.Bifunctor.Free
import Control.Categorical.Bifunctor
import Control.Category.Associative.Free
import Control.Category.Associative

instance (Monoidal i p cat) => Trans2' (FreeMonoidal i p) cat where
    drop2 (FreeMonoidalBaseOp a) = a
    drop2 (FreeMonoidalCategoryOp Id) = id
    drop2 (FreeMonoidalCategoryOp (a :>>> b)) = drop2 a >>> drop2 b
    drop2 (FreeMonoidalBifunctorOp (a :*** b)) = drop2 a *** drop2 b
    drop2 (FreeMonoidalLeftIdentityOp Idl) = idl
    drop2 (FreeMonoidalLeftIdentityOp Coidl) = coidl
    drop2 (FreeMonoidalRightIdentityOp Idr) = idr
    drop2 (FreeMonoidalRightIdentityOp Coidr) = coidr
    drop2 (FreeMonoidalAssociativeOp Coassociate) = coassociate
    drop2 (FreeMonoidalAssociativeOp Associate) = associate