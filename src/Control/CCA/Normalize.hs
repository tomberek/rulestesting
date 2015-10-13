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

cca_rule1 :: (ArrowCCA a) => TExp (a b c) -> (Q (TExp (a b c)))
cca_rule1 [rule2| arr f >>> arr g |] = [|| arr ( $$g . $$f) ||]
     where args :: f~TExp (b ->d ) => g ~ TExp (d -> c) => args
           args = undefined
cca_rule1 a = do
    return a

cca_rule2 :: (ArrowCCA a) => TExp (a (b,d) (c,d)) -> Q (TExp (a (b,d) (c,d)))
cca_rule2 [rule2| first (arr f) |]    = [|| arr ( $$f *** id) ||]
cca_rule2 a = return a

cca_rule3 :: Rule Arrow a b b
cca_rule3 [rule2| arr (\n -> m) |] | error (show (n_,m_)) == n_ = [|| id ||]
cca_rule3 a = return a

type Rule ctx a b c = ctx a => TExp (a b c) -> Q (TExp (a b c))
e :: (ArrowCCA a) => TExp (a (b,d) (c,d)) -> Maybe (Q (TExp (a (b,d) (c,d))))
e = Just . cca_rule2

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

cca_rulesetT :: ArrowCCA a => TExp (a b c) -> Q (Maybe (TExp (a b c)))
cca_rulesetT [rule2| arr f >>> arr g |] = intoR [||  (arr ( $$g . $$f)) ||]
cca_rulesetT [rule2| arr f >>> loopD i g |]    = intoR [|| loopD $$i ( $$g . ($$f *** id) ) ||]
cca_rulesetT [rule2| loopD i f >>> arr g |]    = intoR [|| loopD $$i ( ($$g *** id) . $$f ) ||]
cca_rulesetT [rule2| loopD i f >>> loopD j g |]= intoR [|| loopD ($$i,$$j) ( associate . juggle
                                                 . ($$g *** id) . juggle . ($$f *** id) . coassociate) ||]
cca_rulesetT [rule2| loop (loopD i f) |]       = intoR [|| loopD $$i (trace (juggle . $$f . juggle)) ||]
cca_rulesetT a =  return Nothing --reportWarning ("cca_ruleset: " ++ show a) >>=

cca_rulesetT2 :: ArrowCCA a => TExp (a (b,b1) (c,b1)) -> Q (Maybe (TExp (a (b,b1) (c,b1))))
cca_rulesetT2 [rule2| first (arr f) |]    = intoR [|| arr ( $$f *** id) ||]
cca_rulesetT2 [rule2| first (loopD i f) |]      = intoR [|| loopD $$i (juggle . ($$f *** id) . juggle) ||]

cca_rulesetT3 :: ArrowCCA a => TExp (a (b,c) (b,c)) -> Q (Maybe (TExp (a (b,c) (b,c))))
cca_rulesetT3 [rule2| delay i |]                = intoR [|| loopD $$i swap ||]

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
