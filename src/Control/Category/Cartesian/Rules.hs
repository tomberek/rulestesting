{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
module Control.Category.Cartesian.Rules where

import Prelude hiding (id,(.),snd,fst)
import Control.Category.Rules
import Control.Category.Monoidal.Free
import Control.Category.Monoidal
import Control.Category.Free
import Control.Category
import Control.Categorical.Bifunctor.Free
import Control.Categorical.Bifunctor
import Control.Category.Associative.Free
import Control.Category.Associative
import Control.Category.Structural.Free
import Control.Category.Structural
import Control.Category.Cartesian
import Control.Category.Cartesian.Free

instance (Cartesian i p cat) => Trans2' (FreeCartesian i p) cat where
    drop2 (FreeCartesianBaseOp a) = a
    drop2 (FreeCartesianCategoryOp Id) = id
    drop2 (FreeCartesianCategoryOp (a :>>> b)) = drop2 a >>> drop2 b
    drop2 (FreeCartesianBifunctorOp (a :*** b)) = drop2 a *** drop2 b
    drop2 (FreeCartesianWeakenOp Snd) = snd
    drop2 (FreeCartesianWeakenOp Fst) = fst
    drop2 (FreeCartesianContractOp Diag) = diag
    drop2 (FreeCartesianSymmetricOp Swap) = swap
    drop2 (FreeCartesianLeftIdentityOp Idl) = idl
    drop2 (FreeCartesianLeftIdentityOp Coidl) = coidl
    drop2 (FreeCartesianRightIdentityOp Idr) = idr
    drop2 (FreeCartesianRightIdentityOp Coidr) = coidr
    drop2 (FreeCartesianAssociativeOp Coassociate) = coassociate
    drop2 (FreeCartesianAssociativeOp Associate) = associate