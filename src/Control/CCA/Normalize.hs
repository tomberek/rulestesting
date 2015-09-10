{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
module Control.CCA.Normalize where
import Control.Arrow.CCA
import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Utilities
import Data.Data
import Data.Generics(extQ)

import Control.Arrow
import Control.Category.Associative
import Control.Category.Structural
import Control.Monad
import Control.Category
import Prelude hiding (id,(.))
import System.IO.Unsafe(unsafePerformIO)

cca_rule1 :: (ArrowCCA a) => TExp (a b c) -> Q (TExp (a b c))
cca_rule1 [rule2| arr f >>> arr g |] = [||  (arr ( $$f . $$g)) ||]
    where args :: f~TExp (b ->d ) => g ~ TExp (d -> c) => args
          args = undefined

d :: (ArrowCCA a) => TExp (a b c) -> Maybe (Q (TExp (a b c)))
d = Just . cca_rule1
cca_rule2 :: (ArrowCCA a) => TExp (a (b,d) (c,d)) -> Q (TExp (a (b,d) (c,d)))
cca_rule2 [rule2| first (arr f) |]    = [|| arr ( $$f *** id) ||]
e :: (ArrowCCA a) => TExp (a (b,d) (c,d)) -> Maybe (Q (TExp (a (b,d) (c,d))))
e = Just . cca_rule2

unTypeRule :: (TExp (a b c) -> Q (TExp (a b c))) -> Exp -> Q Exp
unTypeRule rule exp = unTypeQ $ rule g
    where
        g :: TExp (a b c)
        g = TExp exp

cca_rulesetT :: ArrowCCA a =>[ValidRule a]
cca_rulesetT = [ V cca_rule1, V cca_rule2]
dataEQ :: (Data (a b c),Data z, ArrowCCA a) => z -> Q (TExp (a b c))
dataEQ = dataToTExpQ (const Nothing `extQ` d)

data ValidRule a where
    V ::(TExp (a b c) -> Q (TExp (a b c))) -> ValidRule a
applyRule :: ValidRule a -> Exp -> Maybe (Q Exp)
applyRule (V rule) exp = Just $ unTypeQ $ rule (TExp exp)

cca_ruleset :: Exp -> Q Exp
cca_ruleset [rule| arr f >>> arr g |] = [|  (arr ( $f . $g)) |]
cca_ruleset [rule| first (arr f) |]    = [| arr ( $f *** id) |]
cca_ruleset [rule| arr f >>> loopD i g |]    = [| loopD $i ( $g . ($f *** id) ) |]
cca_ruleset [rule| loopD i f >>> arr g |]    = [| loopD $i ( ($g *** id) . $f ) |]
cca_ruleset [rule| loopD i f >>> loopD j g |]= [| loopD ($i,$j) ( associate . juggle
                                               . ($g *** id) . juggle . ($f *** id) . coassociate) |]
cca_ruleset [rule| loop (loopD i f) |]       = [| loopD $i (trace (juggle . $f . juggle)) |]
cca_ruleset [rule| first (loopD i f) |]      = [| loopD $i (juggle . ($f *** id) . juggle) |]
cca_ruleset [rule| delay i |]                = [| loopD $i swap |]
cca_ruleset a = error "total function at cca_ruleset"

prepareRule :: Data a => (a -> Q Exp) -> a -> Maybe (Q Exp)
prepareRule rule exp= distributeQ $ recover (returnQ Nothing) (returnQ exp >>= rule >>= returnQ . Just)
distributeQ a = case unsafePerformIO $ runQ a of
              Nothing -> Nothing
              Just a -> Just (returnQ a)
cca_rules = map prepareRule [cca_ruleset]
prepRules :: Data a => [Exp -> Maybe (Q Exp)] -> a -> Maybe (Q Exp)
prepRules rules = foldl extQ (const Nothing) rules

juggle :: ((t1, t), t2) -> ((t1, t2), t)
juggle ((x, y), z) = ((x, z), y)
--juggle = coassociate . second swap . associate
trace :: ((t1, t2) -> (t, t2)) -> t1 -> t -- pure looping
trace f x = let (y, z) = f (x, z) in y
cross :: (t -> t2) -> (t1 -> t3) -> (t, t1) -> (t2, t3)
cross = (***)
