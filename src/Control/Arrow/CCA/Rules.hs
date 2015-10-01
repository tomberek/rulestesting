{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
module Control.Arrow.CCA.Rules where
import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Utilities

import Control.Arrow hiding (first,second,(***),(&&&))
import Control.Category.Associative
import Control.Category.Structural
import Control.Categorical.Bifunctor
import Control.Category
import Prelude hiding (id,(.))
import qualified Data.Constraint as C
import Control.Category.Rules (category_ruleset)
import Control.Category.Associative.Rules (assoc_ruleset)
import Control.Category.Structural.Rules (struct_ruleset)
import Control.Categorical.Bifunctor.Rules (bifunctor_ruleset)
import Control.Arrow.CCA.Free
import Control.Arrow.CCA.NoQ

catCCA = category $ category_ruleset ++ bifunctor_ruleset ++ assoc_ruleset ++ struct_ruleset ++ cca_ruleset

cca_ruleset = [cca_rulesetT,cca_rulesetT2,cca_rulesetT3,cca_rulesetTerm]
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

cca_rulesetT3 :: RuleE
cca_rulesetT3 [rule| delay i |]                = into [| loopD $i swap |]
cca_rulesetT3 a = nothing

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
