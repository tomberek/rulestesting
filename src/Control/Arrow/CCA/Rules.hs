{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
module Control.Arrow.CCA.Rules where
import Control.Arrow.CCA
import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Utilities

import Control.Arrow
import Control.Category.Associative
import Control.Category.Structural
import Control.Category
import Prelude hiding (id,(.))
import qualified Data.Constraint as C
import Control.Arrow.TH (category)
import Control.Category.Rules (category_ruleset)
import Control.Arrow.TH (ASyn)

catCCA = category $ cca_ruleset ++ category_ruleset

cca_ruleset :: [Exp -> Q (Maybe Exp)]
cca_ruleset = let a = C.Dict :: C.Dict (ArrowCCA (ASyn m))
                  demote = unTypeRule a
              in [demote cca_rulesetT,demote cca_rulesetT2,demote cca_rulesetT3]

cca_rulesetT :: RuleT ArrowCCA a b c
cca_rulesetT [rule2| arr f >>> arr g |] = into [||  (arr ( $$g . $$f)) ||]
cca_rulesetT [rule2| arr f >>> loopD i g |]    = into [|| loopD $$i ( $$g . ($$f *** id) ) ||]
cca_rulesetT [rule2| loopD i f >>> arr g |]    = into [|| loopD $$i ( ($$g *** id) . $$f ) ||]
cca_rulesetT [rule2| loopD i f >>> loopD j g |]= into [|| loopD ($$i,$$j) ( associate . juggle
                                                 . ($$g *** id) . juggle . ($$f *** id) . coassociate) ||]
cca_rulesetT [rule2| loop (loopD i f) |]       = into [|| loopD $$i (trace (juggle . $$f . juggle)) ||]
cca_rulesetT a =  return Nothing

cca_rulesetT2 :: RuleT ArrowCCA a (b,b1) (c,b1)
cca_rulesetT2 [rule2| first (arr f) |]    = into [|| arr ( $$f *** id) ||]
cca_rulesetT2 [rule2| first (loopD i f) |]      = into [|| loopD $$i (juggle . ($$f *** id) . juggle) ||]
cca_rulesetT2 a = return Nothing

cca_rulesetT3 :: RuleT ArrowCCA a (b,c) (b,c)
cca_rulesetT3 [rule2| delay i |]                = into [|| loopD $$i swap ||]
cca_rulesetT3 a = return Nothing

juggle :: ((t1, t), t2) -> ((t1, t2), t)
juggle ((x, y), z) = ((x, z), y)
--juggle = coassociate . second swap . associate
trace :: ((t1, t2) -> (t, t2)) -> t1 -> t -- pure looping
trace f x = let (y, z) = f (x, z) in y
cross :: (t -> t2) -> (t1 -> t3) -> (t, t1) -> (t2, t3)
cross = (***)
