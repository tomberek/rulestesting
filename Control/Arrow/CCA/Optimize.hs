{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}
{- |
Module      :  Control.Arrow.CCA.Optimize
Description :  Optimize ArrowCCA Instances
Copyright   :  (c) 2015 Thomas Bereknyei
License     :  BSD3
Maintainer  :  Thomas Bereknyei <tomberek@gmail.com>
Stability   :  unstable
Portability :  GADTs,TemplateHaskell,MultiParamTypesClasses

Originally from CCA package: <https://hackage.haskell.org/package/CCA-0.1.5.2>
-}
module Control.Arrow.CCA.Optimize
    (norm, normOpt, fromAExp, normalize,normalizeTrace,
    runCCNF, nth', runIt,
    pprNorm, pprNormOpt, printCCA, ASyn(..),AExp(..),ArrowCCA(..),(.),id
    ,reifyAlpha
    --cross, dup, swap, assoc, unassoc, juggle, trace, mirror, untag, tagT, untagT,
    --swapE, dupE
    ) where

import Control.Category.Associative
import Control.Category.Structural
import Control.Category.Monoidal
import Control.Category.Cartesian
import Control.Categorical.Bifunctor

import           Control.Category
import           Prelude             hiding (id, (.),fst,snd)
import           Control.Arrow hiding (first,second,(***),(&&&))
import qualified Control.Arrow as A
import           Control.Arrow.CCA
import           Control.Arrow.TH
import           Control.Monad(liftM)
import           Control.Applicative
import           Data.Char           (isAlpha)
import           Language.Haskell.TH
import           Language.Haskell.TH.Utilities
import           Data.Bitraversable
import           Control.Parallel
import qualified Control.Lens as L
import Control.Lens hiding (Bifunctor)
import qualified Debug.Trace
import Data.Data (Data(..))
import qualified Data.Generics       as G (everywhere, mkT)


-- | norm is a TH function that normalizes a given CCA, e.g., $(norm e) will
-- give the CCNF of e.
norm :: ASyn t t1 t2 -> Q Exp
norm (AExp e) = normalizeQ e >>= fromAExp >>= arrFixer

-- | Two stage normalization. First uses skew-monoidal category rewrite rules (not fully implemented yet)
-- as well as the CCA optimizations (perhaps do CCC first, then CCA?) and then finishes by converting all
-- categorical constructors back into CCA-compatable forms.
normalizeQ :: AExp -> Q AExp
normalizeQ input = Debug.Trace.trace (show input ++ "  <--  starting") $ L.rewriteM (normalizeReifyAlpha normalizeTrace) input
               >>= L.rewriteM (normalizeReifyAlpha normalizeA)

-- | Finds all instances of patterns that match the rule-set and converts Arr's to categorical operators if possible.
normalizeReifyAlpha :: (AExp -> AExp) -> AExp -> Q (Maybe AExp)
normalizeReifyAlpha _ (Arr e) = findM (\(a,b) -> ifM (areExpAEq' e a) (return $ Just b) $ return Nothing) rules
normalizeReifyAlpha normRules e = ifM (eqM e n) (return Nothing) (return $ Just n)
                        where n = normRules e

-- normOpt returns the pair of state and pure function as (s, f) from optimized
-- CCNF in the form loopD i (arr f).
normOpt :: ASyn m a b -> ExpQ
normOpt (AExp e) = do
    e' <- normalizeQ e
    case e' of
      LoopD i f -> tupE [i, f]
      Arr f     -> [| ( (), $(f) ) |]
      ArrM f  -> [| ( (), $(f) ) |]
      --g -> [| ( (), $(fromAExp g) ) |] -- perhaps just expose best effort function?
      g -> error $ "Perhaps not causual? Can't optimize past: " ++ show g

-- CCNF
-- ====
-- | Easy way to turn on tracing
normalizeTrace :: AExp -> AExp
normalizeTrace e = let n = normalize e
                   in if n==e then Debug.Trace.trace (show e ++ "    ===>    *") $ n
                      else Debug.Trace.trace (show e ++ "    ===>    " ++ show n) $ n
--normalizeTrace e = normalize e

-- Arrow, CCA, and skew-mondoidal category laws (not yet all of them):
normalize :: AExp -> AExp

-- | Category
normalize (f :>>> Id) = f
normalize (Id :>>> f) = f
normalize (Id :*** f) = Second f
normalize (f :*** Id) = First f
normalize (First Id) = Id
normalize (Second Id) = Id
normalize (Lft Id) = Id

-- | Terminal
--normalize (f :>>> Terminate) = Terminate
--normalize (f :>>> (Terminate :*** Terminate)) = Terminate :*** Terminate
--normalize (f :>>> (Terminate :&&& Terminate)) = Terminate :&&& Terminate

-- Cartesian
normalize (Diag :>>> Fst) = Id
normalize (Diag :>>> Snd) = Id

normalize (Diag :>>> (f :*** g) ) = f :&&& g  -- not sound?
normalize ((Fst :>>> f) :&&& (Snd :>>> g)) = f :*** g
normalize ((Snd :>>> f) :&&& (Fst :>>> g)) = g :*** f
normalize ((f :*** g) :>>> Snd) = Snd :>>> g
normalize ((f :*** g) :>>> Fst) = Fst :>>> f
normalize ((f :&&& g) :>>> Snd) = g
normalize ((f :&&& g) :>>> Fst) = f
normalize (Fst :&&& Snd) = Id :*** Id
normalize (Snd :&&& Fst) = Swap :>>> Id :*** Id
normalize ((Fst :>>> f) :&&& Snd) = f :*** Id
normalize ((Snd :>>> f) :&&& Fst) = Swap :>>> f :*** Id
normalize (Fst :&&& (Snd :>>> f)) = Id :*** f
normalize (Snd :&&& (Fst :>>> f)) = Swap :>>> Id :*** f
normalize (Id :&&& Id) = Diag
normalize ((f :&&& g) :>>> Swap) = g :&&& f
normalize (Id :&&& g) = Diag :>>> Second g
normalize (f :&&& Id) = Diag :>>> First f
normalize ((Diag :>>> f) :&&& (Diag :>>> g)) = Diag :>>> (f :&&& g)

-- | Associative. Probably not handy yet
{-normalize ( Second Disassociate :>>> Disassociate :>>> First Disassociate ) = Disassociate :>>> Disassociate
normalize ( First Associate :>>> Associate :>>> Second Associate ) = Associate :>>> Associate
normalize ( First Swap :>>> Associate :>>> Second Swap) = Associate :>>> Swap :>>> Associate
normalize ( Second Swap :>>> Associate :>>> First Swap) = Associate :>>> Swap :>>> Associate
---}
-- Braided
normalize (Diag :>>> ArrM f) = ArrM ( [| diagE . $f |])
normalize (Swap :>>> Swap) = Id
normalize (Swap :>>> Fst) = Snd
normalize (Swap :>>> Snd) = Fst
normalize (Diag :>>> Swap) = Diag
normalize (Swap :>>> Swap :>>> f) = f
normalize (Swap :>>> Fst :>>> f) = Snd :>>> f
normalize (Swap :>>> Snd :>>> f) = Fst :>>> f
normalize (Diag :>>> Swap :>>> f) = Diag :>>> f
normalize ((f :*** g) :>>> Swap) = Swap :>>> (g :*** f)  -- bubble Swap to the left
normalize ((f :*** g) :>>> (h :*** i)) = (f :>>> h) :*** (g :>>> i) -- combine sequential ***
normalize ((f :&&& g) :>>> (h :*** i)) = (f :>>> h) :&&& (g :>>> i) -- combine &&& followed by ***
normalize ((h :>>> (f :*** g)) :>>> Swap) = h :>>> Swap :>>> (g :*** f) -- bubble swap to the left

-- Never a problem combining Diag with Arr, no rules have Diag on the right.
normalize (Diag :>>> Arr f) = Arr ( f `o` diagE)

normalize ((Diag :>>> First f) :>>> Swap) = Diag :>>> Second f
normalize ((Diag :>>> Second f) :>>> Swap) = Diag :>>> First f
normalize (First f :>>> Swap) = Swap :>>> Second f
normalize (Second f :>>> Swap) = Swap :>>> First f

-- Association of >>>. Not sure if needed or helpful.
normalize (f :>>> (g :>>> h)) = (f :>>> g) :>>> h -- Added by TOM
normalize ((f :>>> g) :>>> h) = (f :>>> g) :>>> h -- Added by TOM
normalize e = e

-- | Round 2 is CCA and assoc in other direction
normalizeA :: AExp -> AExp
-- | CCA
normalizeA (Arr f :>>> Arr g) = Arr (g `o` f)
normalizeA (Arr f :>>> LoopD i g) = LoopD i (g `o` (f `crossE` idE))
normalizeA (LoopD i f :>>> Arr g) = LoopD i ((g `crossE` idE) `o` f)
normalizeA (LoopD i f :>>> LoopD j g) = LoopD (tupE [i,j])
  (assocE `o` juggleE `o` (g `crossE` idE) `o` juggleE `o` (f `crossE` idE) `o` assocE')
normalizeA (Loop (LoopD i f)) = LoopD i (traceE (juggleE `o` f `o` juggleE))
normalizeA (First (LoopD i f)) = LoopD i (juggleE `o` (f `crossE` idE) `o` juggleE)
normalizeA (Delay i) = LoopD i swapE
-- Choice:
normalizeA (Lft (Arr f)) = Arr (lftE f)
normalizeA (Lft (LoopD i f)) = LoopD i (untagE `o` lftE f `o` tagE)

normalizeA (Loop (Arr f)) = Arr (traceE f) -- Not in original CCA. 2015-TB Added by TOM: for rec?
normalizeA (Loop (ArrM f)) = ArrM (traceE f) -- Not in original CCA. 2015-TB Added by TOM: for rec?

-- Laws for effectful ArrM's
normalizeA (Arr f :>>> ArrM g) = ArrM [| $g . $f |]
normalizeA (ArrM f :>>> Arr g) = ArrM [| liftM $g . $f |]
normalizeA (First (ArrM f)) = ArrM ( f `crossME` [|return|] )
normalizeA (Second (ArrM f)) = ArrM ( [|return|] `crossME` f )
--normalize (LoopD i f :>>> ArrM g) = LoopD i ((g `crossME` [|return|]) `o` f) --TODO: check this, perhaps need a LoopDM?

-- | ASSUMPTION: We presume that pure actions are fairly cheap to perform, thus not much to gain by *** or &&&
normalizeA (Arr f :*** Arr g) = Arr $ f `crossE` g
normalizeA (ArrM f :*** Arr g) = ArrM $ f `crossME` [| return . $g |]
normalizeA (Arr f :*** ArrM g) = ArrM $ [| return . $f |]  `crossME` g
--normalizeA (ArrM f :*** ArrM g) = ArrM $ f `crossME` g

normalizeA (Arr f :&&& Arr g) = Arr $ (f `crossE` g) `o` diagE
normalizeA (ArrM f :&&& Arr g) = ArrM $ (f `crossME` [| return . $g |]) `o` diagE
normalizeA (Arr f :&&& ArrM g) = ArrM $ ([| return . $f |]  `crossME` g) `o` diagE
normalizeA (f :>>> (g :>>> h)) = f :>>> (g :>>> h) -- Added by TOM
normalizeA ((f :>>> g) :>>> h) = f :>>> (g :>>> h) -- Added by TOM

--normalizeA Id = Arr idE
--normalizeA Diag = Arr diagE
--normalizeA Swap = Arr swapE
--normalizeA Fst = Arr [|fst|]
--normalizeA Snd = Arr [|snd|]
normalizeA f = normalize f


-- | Used to take the function produced by normOpt and process a stream.
-- TODO: explain various arguments, state etc.
-- `e` is the initial state, [b] is input stream
-- The function will only match if it is in LoopD form.
runCCNF :: e -> ((b, e) -> (c, e)) -> [b] -> [c]
runCCNF i f = g i
        where
            g _ [] = []
            g j (x:xs) = let (y, j') = f (x, j)
                            in y : g j' xs

-- | Runs the output function of normOpt and runs it n times.
nth' :: Int -> (b, ((), b) -> (a, b)) -> a
nth' n (i, f) = aux n i
  where
    aux m j = x `seq` if m == 0 then x else aux (m-1) j'
      where (x, j') = f ((), j)

-- | Runs the output function of normOpt once.
runIt :: t -> (b, ((), b) -> (a, b)) -> a
runIt _ = nth' 0

-- Auxiliary Functions
-- ===================

--dup :: t -> (t, t)
--dup x = (x, x)
-- in Control.Category.Monoidal
--swap :: (t1, t) -> (t, t1)
--swap (x, y) = (y, x)
unassoc :: (t1, (t2, t)) -> ((t1, t2), t)
unassoc (x, (y, z)) = ((x, y), z)
assoc :: ((t, t1), t2) -> (t, (t1, t2))
assoc ((x, y), z) = (x, (y, z))
juggle :: ((t1, t), t2) -> ((t1, t2), t)
juggle ((x, y), z) = ((x, z), y)

trace :: ((t1, t2) -> (t, t2)) -> t1 -> t -- pure looping
trace f x = let (y, z) = f (x, z) in y
-- need a traceM?

cross :: (t -> t2) -> (t1 -> t3) -> (t, t1) -> (t2, t3)
cross = bimap

-- | Uses whatever Applicative instance for ArrM *** ArrM combining.
-- Look into Control.Concurrent.Async or
-- newtype Pair a = Pair a deriving (Functor)
-- instance Applicative Pair where
--      pure a = Pair a
--      Pair fs <*> Pair as = Pair $ (\(f,a) -> f a) $ fs `par` (as `pseq` (fs,as))
crossM :: Applicative m => (t -> m t2) -> (t1 -> m t3) -> (t, t1) -> m (t2,t3)
crossM f g =uncurry (liftA2 (,)) . bimap f g

lft :: (t -> a) -> Either t b -> Either a b
lft f x = case x of
  Left  u -> Left (f u)
  Right u -> Right u
tagT :: (Either t t1, t2) -> Either (t, t2) (t1, t2)
tagT (x, y) = case x of
  Left  u -> Left  (u, y)
  Right u -> Right (u, y)
untagT :: Either (a, t) (b, t) -> (Either a b, t)
untagT z = case z of
  Left  (x, y) -> (Left  x, y)
  Right (x, y) -> (Right x, y)

o :: ExpQ -> ExpQ -> ExpQ
f `o` g = infixE (Just g) [|(>>>)|] (Just f) -- appE (appE [|(.)|] f) g
--fromAExp (f :>>> g) = infixE (Just (fromAExp f)) [|(>>>)|] (Just (fromAExp g))
crossE :: ExpQ -> ExpQ -> ExpQ
f `crossE` g = appE (appE [|cross|] f) g

crossME :: ExpQ -> ExpQ -> ExpQ
f `crossME` g = appE (appE [|crossM|] f) g

idE,diagE,swapE,assocE,assocE',juggleE,tagE,untagE :: ExpQ
idE = [|id|]
diagE = [|diag|]
swapE = [|swap|]
assocE = [|assoc|]
assocE' = [|unassoc|]
juggleE = [|juggle|]
tagE = [|tagT|]
untagE = [|untagT|]

traceE,lftE :: ExpQ -> ExpQ
traceE = appE [|trace|]
lftE = appE [|lft|]

-- pprNorm and pprNormOpt return the pretty printed normal forms as a
-- string.
pprNorm :: ASyn m a b -> Q Exp
pprNorm = ppr' . norm

pprNormOpt :: ASyn m a b -> Q Exp
pprNormOpt = ppr' . normOpt
ppr' :: Q Exp -> Q Exp
ppr' e = runQ (fmap toLet e) >>= litE . StringL . simplify . pprint

-- To Let-Expression
-- =================

-- Transform function applications to let-expressions.
--   (\x -> e1) e2  === let x = e2 in e1
toLet :: Exp -> Exp
toLet = G.everywhere (G.mkT aux)
  where
    aux (AppE (LamE [pat] body) arg) = LetE [ValD pat (NormalB arg) []] body
    aux (AppE (LamE (pat:ps) body) arg) = LamE ps (LetE [ValD pat (NormalB arg) []] body)
    aux x = x
