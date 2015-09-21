{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}
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
bifunctor_ruleset = []-- bifunctor_id_f,bifunctor_f_id,bifunctor_diag] --bifunctor_arr]

bifunctor_id_f :: RuleE
bifunctor_id_f [rule| bimap id f |] = into [| second $f |]
bifunctor_id_f [rule| id *** f |]   = into [| second $f |]
bifunctor_id_f [rule| fst &&& (snd >>> f) |] = into [| second $f |]
bifunctor_id_f _ = return Nothing

bifunctor_f_id :: RuleE
bifunctor_f_id [rule| bimap id f |] = into [| first $f |]
bifunctor_f_id [rule| id *** f |]   = into [| first $f |]
bifunctor_f_id [rule| (fst >>> f) &&& snd |] = into [| first $f |]
bifunctor_f_id _ = return Nothing

bifunctor_diag :: RuleE
bifunctor_diag [rule| (fst >>> f) &&& (snd >>> g) |] = into [| $f *** $g |]
bifunctor_diag _ = return Nothing

bifunctor_arr :: RuleE
bifunctor_arr [rule| arr (\(x,y) -> (a,z)) |] | x_ == a_ = into [| second (arr (\ $y -> $z)) |]
                                              | y_ == z_ = into [| first (arr (\ $x -> $a)) |]
bifunctor_arr _ = return Nothing
