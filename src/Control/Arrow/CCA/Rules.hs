{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
module Control.Arrow.CCA.Rules where
import Language.Haskell.TH
import Language.Haskell.TH.Quote
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Utilities

import Control.Arrow hiding (first,second,(***),(&&&))
import Control.Category.Associative
import Control.Category.Structural
import Control.Categorical.Bifunctor
import Control.Category
import Prelude hiding (id,(.))
import Control.Category.Rules (category_ruleset,category_ruleset')
import Control.Category.Associative.Rules (assoc_ruleset)
import Control.Category.Structural.Rules (struct_ruleset)
import Control.Categorical.Bifunctor.Rules (bifunctor_ruleset)
import Control.Arrow.CCA.Free
import Data.Functor.Identity
import Data.Generics.Multiplate
import Control.Arrow.CCA
import Control.Monad
import Control.Applicative

toExpCCA :: FreeCCA m i p k a b -> ExpQ
toExpCCA a = do
    a' <- foldFor catplate toExp' a
    --reportError $ show a
    foldM transformExp a' all_cca

catCCA :: QuasiQuoter
catCCA = category all_cca

all_cca :: [[RuleE]]
all_cca = [category_ruleset ++ bifunctor_ruleset ++ assoc_ruleset ++ struct_ruleset,
                                category_ruleset' ++ bifunctor_ruleset ++ assoc_ruleset ++ struct_ruleset,
                                category_ruleset ++ cca_ruleset,
                                category_ruleset' ++ cca_ruleset,
                                [cca_ruleset_arr]]

cca_ruleset,cca_ruleset' :: [RuleE]
cca_ruleset' = [cca_rulesetT,cca_rulesetT2,cca_rulesetT3,cca_rulesetTerm]
cca_ruleset = [cca_rulesetT,cca_rulesetT2,cca_rulesetT2a,cca_rulesetT3,cca_rulesetT4,cca_rulesetTerm,cca_rulesetArrM]


cca_ruleset_arr :: RuleE
cca_ruleset_arr [rule| arr f |] = into [| arr' (returnQ $(lift f_)) $f |]
cca_ruleset_arr [rule| arrM f |] = into [| arrM' (returnQ $(lift f_)) $f |]
cca_ruleset_arr [rule| delay f |] = into [| delay' (returnQ $(lift f_)) $f |]
cca_ruleset_arr [rule| terminate f |] = into [| terminate' (returnQ $(lift f_)) $f |]
cca_ruleset_arr _ = nothing

cca_rulesetT :: RuleE
cca_rulesetT [rule| arr f >>> arr g |] = into [|  arr ( $g . $f) |]
cca_rulesetT [rule| arr f >>> loopD i g |]    = into [| loopD $i ( $g . ($f *** id) ) |]
cca_rulesetT [rule| loopD i f >>> arr g |]    = into [| loopD $i ( ($g *** id) . $f ) |]
cca_rulesetT [rule| loopD i f >>> loopD j g |]= into [| loopD ($i,$j) ( associate . juggle
                                                 . ($g *** id) . juggle . ($f *** id) . coassociate) |]
cca_rulesetT [rule| loop (loopD i f) |]       = into [| loopD $i (trace (juggle . $f . juggle)) |]
cca_rulesetT a = nothing

cca_rulesetT2 :: RuleE
cca_rulesetT2 [rule| first (arr f) |]   = into [| arr ( $f *** id) |]
cca_rulesetT2 [rule| first (loopD i f) |] = into [| loopD $i (juggle . ($f *** id) . juggle) |]
cca_rulesetT2 a = nothing

cca_rulesetT2a :: RuleE
cca_rulesetT2a [rule| second f |] = into [| swap >>> first $f >>> swap |]
cca_rulesetT2a [rule| f *** loopD i g |] = into [| first $f >>> second (loopD $i $g) |]
cca_rulesetT2a [rule| (f *** g) >>> loopD i h |] = into [| first $f >>> second $g >>> loopD $i $h |]
cca_rulesetT2a [rule| loopD i g *** f |] = into [| second $f >>> first (loopD $i $g) |]
cca_rulesetT2a [rule| f *** loop g |] = into [| first $f >>> second (loop $g) |]
cca_rulesetT2a [rule| loop g *** f |] = into [| second $f >>> first (loop $g) |]
cca_rulesetT2a _ = nothing

cca_rulesetT3 :: RuleE
cca_rulesetT3 [rule| delay i |]                = into [| loopD $i swap |]
cca_rulesetT3 a = nothing

isArrLike :: Exp -> Bool
isArrLike (VarE (nameBase -> "diag")) = True
isArrLike (VarE (nameBase -> "swap")) = True
isArrLike (VarE (nameBase -> "fst")) = True
isArrLike (VarE (nameBase -> "snd")) = True
isArrLike _ = False

cca_rulesetT4 :: RuleE
cca_rulesetT4 [rule| first f |] | isArrLike f_ = into [| arr ($f *** id) |]
                                | otherwise = nothing
cca_rulesetT4 [rule| second f |] | isArrLike f_ = into [| arr (id *** $f) |]
                                 | otherwise = nothing
cca_rulesetT4 [rule| f >>> arr g |] | isArrLike f_ = into [| arr ( $g . $f ) |]
                                    | otherwise = nothing
cca_rulesetT4 [rule| arr f >>> g |] | isArrLike g_ = into [| arr ( $g . $f ) |]
                                    | otherwise = nothing
cca_rulesetT4 [rule| f >>> loopD i g |] | isArrLike f_ = into [| loopD $i ( $g . ($f *** id) ) |]
                                        | otherwise = nothing
cca_rulesetT4 [rule| loopD i f >>> g |] | isArrLike g_ = into [| loopD $i ( ($g *** id) . $f ) |]
                                        | otherwise = nothing
cca_rulesetT4 a = nothing

cca_rulesetArrM :: RuleE
cca_rulesetArrM [rule| arr f >>> arrM g |] = into [| arrM ($g . $f) |]
cca_rulesetArrM [rule| arrM f >>> arr g |] = into [| arrM (liftM $g . $f) |]
cca_rulesetArrM [rule| first (arrM f) |] = into [| arrM ($f `crossM` return) |]
cca_rulesetArrM [rule| second (arrM f) |] = into [| arrM (return `crossM` $f) |]
cca_rulesetArrM _ = nothing

cca_rulesetTerm :: RuleE
cca_rulesetTerm [rule| f >>> terminate g |] = into [| terminate $g |] -- unsound? removes effects?
cca_rulesetTerm [rule| f >>> (terminate h *** terminate g) |] = into [| terminate $h *** terminate $g |] -- unsound? removes effects?
cca_rulesetTerm [rule| f >>> (terminate h &&& terminate g) |] = into [| terminate $h &&& terminate $g |] -- unsound? removes effects?
cca_rulesetTerm _ = nothing

juggle :: ((t1, t), t2) -> ((t1, t2), t)
juggle ((x, y), z) = ((x, z), y)
--juggle = coassociate . second swap . associate
trace :: ((t1, t2) -> (t, t2)) -> t1 -> t -- pure looping
trace f x = let (y, z) = f (x, z) in y
cross :: (t -> t2) -> (t1 -> t3) -> (t, t1) -> (t2, t3)
cross = (***)
crossM :: Applicative m => (t -> m t2) -> (t1 -> m t3) -> (t, t1) -> m (t2,t3)
crossM f g =uncurry (liftA2 (,)) . cross f g
