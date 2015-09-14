{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
module Control.CCA.Normalize where
import Control.Arrow.CCA
import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Utilities
import Data.Data
import Data.Generics(extQ)

import Control.Arrow
import Control.Applicative
import Control.Category.Associative
import Control.Category.Structural
import Control.Monad
import Control.Category
import Prelude hiding (id,(.))
import System.IO.Unsafe(unsafePerformIO)
import qualified Data.Constraint as C
import qualified Data.Constraint.Unsafe as C
import qualified Data.Constraint.Forall as C
import Unsafe.Coerce
import Control.Arrow.CCA.Optimize

cca_rule1 :: (ArrowCCA a) => TExp (a b c) -> Q (TExp (a b c))
cca_rule1 [rule2| arr f >>> arr g |] = [||  (arr ( $$f . $$g)) ||]
    where args :: f~TExp (b ->d ) => g ~ TExp (d -> c) => args
          args = undefined

d :: (ArrowCCA a) => (TExp (a b c) -> Maybe (Q (TExp (a b c))))
d = Just . cca_rule1

d2 :: Exp -> Q Exp
d2 = \texp -> unTypeQ $ cca_rule1 $ (TExp texp :: TExp (ASyn m a b))

d2a = d3 (C.Dict :: C.Dict (ArrowCCA (ASyn m))) cca_rule1
-- | Needs a free proxy to untyp TExp
-- Usage: (d3 (Id :: ASyn m a b) cca_rule1) :: Exp -> Q Exp
d3 :: C.Dict (ctx a) -> (ctx a => TExp (a b c) -> Q (TExp (a b c))) -> Exp -> Q Exp
d3 C.Dict rule texp = unTypeQ $ rule $ TExp (texp )

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
dataEQ :: (Data (a b c), ArrowCCA a) => TExp (a b c) -> Q (TExp (a b c))
dataEQ = dataToTExpQ (const Nothing `extQ` d)

data ValidRule a where
    V ::(TExp (a b c) -> Q (TExp (a b c))) -> ValidRule a
applyRule :: ValidRule a -> Exp -> Maybe (Q Exp)
applyRule (V rule) exp = Just $ unTypeQ $ rule (TExp exp)

cca_ruleset :: Exp -> Q (Maybe Exp)
cca_ruleset [rule| arr f >>> arr g |] = intoR [|  (arr ( $g . $f)) |]
cca_ruleset [rule| first (arr f) |]    = intoR [| arr ( $f *** id) |]
cca_ruleset [rule| arr f >>> loopD i g |]    = intoR [| loopD $i ( $g . ($f *** id) ) |]
cca_ruleset [rule| loopD i f >>> arr g |]    = intoR [| loopD $i ( ($g *** id) . $f ) |]
cca_ruleset [rule| loopD i f >>> loopD j g |]= intoR [| loopD ($i,$j) ( associate . juggle
                                               . ($g *** id) . juggle . ($f *** id) . coassociate) |]
cca_ruleset [rule| loop (loopD i f) |]       = intoR [| loopD $i (trace (juggle . $f . juggle)) |]
cca_ruleset [rule| first (loopD i f) |]      = intoR [| loopD $i (juggle . ($f *** id) . juggle) |]
cca_ruleset [rule| delay i |]                = intoR [| loopD $i swap |]
cca_ruleset a =  return Nothing --reportWarning ("cca_ruleset: " ++ show a) >>= 

intoR = fmap Just

prepRules :: Data a => [Exp -> Q Exp] -> a -> Q (Maybe Exp)
prepRules rules a =
    recover (returnQ Nothing) $ foldl extQ (const $ returnQ Nothing) (map r rules) a
    where r rule e = Just <$> rule e

juggle :: ((t1, t), t2) -> ((t1, t2), t)
juggle ((x, y), z) = ((x, z), y)
--juggle = coassociate . second swap . associate
trace :: ((t1, t2) -> (t, t2)) -> t1 -> t -- pure looping
trace f x = let (y, z) = f (x, z) in y
cross :: (t -> t2) -> (t1 -> t3) -> (t, t1) -> (t2, t3)
cross = (***)
