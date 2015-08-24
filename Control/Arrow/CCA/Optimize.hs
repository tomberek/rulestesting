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
    (norm, normOpt, fromAExp, normalize,
    runCCNF, nth', runIt,
    pprNorm, pprNormOpt, printCCA, ASyn(..),AExp(..),ArrowCCA(..),(.),id
    --cross, dup, swap, assoc, unassoc, juggle, trace, mirror, untag, tagT, untagT,
    --swapE, dupE
    ) where

import           Control.Category
import           Prelude             hiding (id, (.))
import           Control.Arrow
import           Control.Arrow.CCA
import           Control.Arrow.TH
import           Control.Monad(liftM)
import           Control.Applicative
import           Data.Char           (isAlpha)
import           Language.Haskell.TH
import           Language.Haskell.TH.Utilities
import qualified Control.Lens as L
import Control.Lens
import qualified Debug.Trace
import Data.Data (Data(..))
import qualified Data.Generics       as G (everywhere, mkT)

-- Internal Representation
-- =======================

-- We use AExp to syntactically represent an arrow for normalization purposes.
data AExp
  = Arr ExpQ
  | First AExp
  | AExp :>>> AExp
  | ArrM ExpQ -- added to allow arrows with side effects
  | AExp :*** AExp -- added to prevent premature optimization? or to allow it?
  | AExp :&&& AExp -- added to prevent premature optimization? or to allow it?
  | Loop AExp       -- simple loop, needed for rec?
  | LoopD ExpQ ExpQ -- loop with delayed feedback
  | Delay ExpQ
  | Lft AExp

  | ArrFirst ExpQ -- allows for two stages of optimization
  | ArrSecond ExpQ -- allows for two stages of optimization

  | Id -- This and below added for Symetric Cartesian (not monoidal)
  -- Cartesian
  | Diag
  | Fst
  | Snd
  -- Associative (not used much yet)
  | Associate
  | Disassociate
  -- Braided and Symmetric
  | Swap
  | Second AExp
  {- Closed, not needed
  | Apply -- (f,a) = f a   arr (\(f,a)->f a)
  | Curry
  | Uncurry
  -- Monoidal, not needed
  | Idr
  | Idl
  | Coidl
  | Coidr
  -}

instance L.Plated AExp where
    plate f (First e) = First <$> f e
    plate f (Second e) = Second <$> f e
    plate f (a :>>> b) = (:>>>) <$> f a <*> f b
    plate f (a :*** b) = (:***) <$> f a <*> f b
    plate f (a :&&& b) = (:&&&) <$> f a <*> f b
    plate f (Loop e) = Loop <$> f e
    plate f (Lft e) = Lft <$> f e
    plate _ e = pure e

areExpAEq' :: Q Exp -> Q Exp -> Q Bool
areExpAEq' f g = do
    f' <- liftM fixity f
    g' <- liftM fixity g
    case f' of
        UInfixE {} -> return False
        _ -> case g' of
             UInfixE {} -> return False
             _ -> expEqual f' g'

fixity :: Data a => a -> a
fixity = G.everywhere (G.mkT expf)
    where expf (UInfixE l op r) = InfixE (Just l) op (Just r)
          expf e = e

-- | Used to measure progress for normalization using rewriteM
eqM :: AExp -> AExp -> Q Bool
eqM (Arr f) (Arr g) = areExpAEq' f g
eqM (ArrFirst f) (ArrFirst g) = areExpAEq' f g
eqM (ArrSecond f) (ArrSecond g) = areExpAEq' f g
eqM (First f) (First g) = eqM f g
eqM (Second f) (Second g) = eqM f g
eqM (f :>>> g) (h :>>> i) = (&&) <$> eqM f h <*> eqM g i
eqM (ArrM f) (ArrM g) = areExpAEq' f g
eqM (f :*** g) (h :*** i) = (&&) <$> eqM f h <*> eqM g i
eqM (f :&&& g) (h :&&& i) = (&&) <$> eqM f h <*> eqM g i
eqM (Loop f) (Loop g) = eqM f g
eqM (LoopD f g) (LoopD h i) = (&&) <$> areExpAEq' f h <*> areExpAEq' g i
eqM (Delay f) (Delay g) = areExpAEq' f g
eqM (Lft f) (Lft g) = eqM f g
eqM Id Id = return True
eqM Diag Diag = return True
eqM Fst Fst = return True
eqM Snd Snd = return True
eqM Associate Associate = return True
eqM Disassociate Disassociate = return True
eqM Swap Swap = return True
eqM _ _ = return False

infixr 1 :>>>
infixr 3 :***
infixr 3 :&&&

instance Show AExp where
    show Id = "Id"
    show Diag = "Diag"
    show Swap = "Swap"
    show Fst = "Fst"
    show Snd = "Snd"
    show Associate = "Associate"
    show Disassociate = "Disassociate"
    show (Arr _) = "Arr"
    show (First f) = "First " ++ show f
    show (Second f) = "Second " ++ show f
    show (ArrFirst _) = "ArrFirst"
    show (ArrSecond _) = "ArrSecond"
    show (ArrM _) = "ArrM"
    show (f :>>> g) = "(" ++ show f ++ " >>> " ++ show g ++ ")"
    show (f :*** g) = "[" ++ show f ++ " *** " ++ show g ++ "]"
    show (f :&&& g) = "[" ++ show f ++ " &&& " ++ show g ++ "]"
    show (Loop f) = "Loop " ++ show f
    show (LoopD _ _) = "LoopD"
    show (Delay _) = "Delay"
    show (Lft _) = "Lft"
instance Show (ASyn m a b) where
    show (AExp x) = show x

-- We use phantom types to make ASyn an Arrow.
newtype ASyn (m :: * -> *) b c = AExp AExp

instance Category (ASyn m) where
    id = AExp Id
    AExp g . AExp f = AExp (f :>>> g)
instance Arrow (ASyn m) where
    arr _ = error "ASyn arr not implemented"
    first (AExp f) = AExp (First f)
    second (AExp f) = AExp (Second f)
    (AExp f) *** (AExp g) = AExp (f :*** g)
    (AExp f) &&& (AExp g) = AExp (f :&&& g)
instance ArrowLoop (ASyn m) where
    loop (AExp f) = AExp (Loop f)
instance ArrowCCA (ASyn m) where
    arr' f _ = AExp (Arr f)
    delay _ = error "ASyn delay not implemented"
    delay' f _ = AExp (Delay f)
    type M (ASyn m) = m  -- Not in original CCA. 2015-TB
    arrM' f _ = AExp (ArrM f)
    arrM _ = error "ASyn arrM not implemented"
--ArrowChoice only requires definition for 'left', but the default implementation
--for 'right' and '|||' uses arr so we need to redefine them using arr' here.
--'+++' is also redefined here for completeness.
instance Monad m => ArrowChoice (ASyn m) where
    left (AExp f) = AExp (Lft f)
    right f = arr' [| mirror |] mirror >>> left f >>> arr' [| mirror |] mirror
    f +++ g = left f >>> right g
    f ||| g = f +++ g >>> arr' [| untag |] untag

-- Pretty printing AExp.
printCCA :: ASyn m t t1 -> IO ()
printCCA (AExp x) = runQ (fromAExp x) >>= putStrLn . simplify . pprint

-- Normalization
-- =============
-- Captures the expressions (using th-alpha's notion of equivalence) for
-- conversion into categorical terms.
rules :: [(ExpQ, AExp)]
rules = [
        ([| \a -> a |],Id)
        , ([| arr id |],Id)
        , ([| returnA |],Id)
        , ([| id |],Id)
        , ([| \(a,b) -> (a,b)|],Id)
        , ([| \(a,(b,c)) -> (a,(b,c))|],Id)
        , ([| \((a,b),c) -> ((a,b),c)|],Id) -- so far only two levels
        , ([| \a -> (a,a)|],Diag)
        , ([| \(a,b) -> a|],Fst)
        , ([| arr fst |],Fst)
        , ([| \(a,b) -> b|],Snd)
        , ([| arr snd |],Snd)
        , ([| \(a,b) -> (b,a)|],Swap)
        , ([| arr (\(a,b) -> (b,a))|],Swap)
        , ([| \(a,(b,c)) -> ((a,b),c)|],Disassociate)
        , ([| \((a,b),c) -> (a,(b,c))|],Associate) -- so far only first levels
        ]

-- | Monadic Find, coppied from another library (sorry, forgot which)
findM :: Monad m => (a -> m (Maybe t)) -> [a] -> m (Maybe t)
findM f = foldr test (return Nothing)
    where test x m = do
              curr <- f x
              maybe m (const $ return curr) curr

-- | norm is a TH function that normalizes a given CCA, e.g., $(norm e) will
-- give the CCNF of e.
norm :: ASyn t t1 t2 -> Q Exp
norm (AExp e) = normalizeQ e >>= fromAExp >>= arrFixer

-- | Two stage normalization. First uses skew-monoidal category rewrite rules (not fully implemented yet)
-- as well as the CCA optimizations (perhaps do CCC first, then CCA?) and then finishes by converting all
-- categorical constructors back into CCA-compatable forms.
normalizeQ :: AExp -> Q AExp
normalizeQ input = L.rewriteM (normalizeReifyAlpha normalize) input
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

-- | fromAExp converts AExp back to TH Exp structure.
fromAExp :: AExp -> ExpQ

fromAExp Id = [|arr id|] -- Categorical constructors should not be around after second stage
fromAExp Diag = [| arr dup |]
fromAExp Fst = [| arr fst |]
fromAExp Snd = [| arr snd |]
fromAExp Associate = [| arr (\((a,b),c)->(a,(b,c))) |]
fromAExp Disassociate = [| arr (\(a,(b,c))->((a,b),c)) |]
fromAExp Swap = [| arr swap |]

-- Should not be arround after second rewrite pass:
fromAExp (ArrFirst f) = appE [|arr|] f
fromAExp (ArrSecond f) = appE [|arr|] f

fromAExp (Arr f) = appE [|arr|] f
fromAExp (First f) = appE [|first|] (fromAExp f)
fromAExp (Second f) = appE [|second|] (fromAExp f)
fromAExp (f :>>> g) = infixE (Just (fromAExp f)) [|(>>>)|] (Just (fromAExp g))
fromAExp (Loop f) = appE [|loop|] (fromAExp f)
fromAExp (LoopD i f) = appE (appE [|loopD|] i) f
fromAExp (ArrM i) = appE [|arrM|] i
fromAExp (Delay i) = appE [|delay|] i
fromAExp (Lft f) = appE [|left|] (fromAExp f)
fromAExp (f :*** g) = infixE (Just (fromAExp f)) [|(***)|] (Just (fromAExp g)) -- Not in original CCA. 2015-TB
fromAExp (f :&&& g) = infixE (Just (fromAExp f)) [|(&&&)|] (Just (fromAExp g)) -- Not in original CCA. 2015-TB

-- CCNF
-- ====
-- | Easy way to turn on tracing
normalizeTrace :: AExp -> AExp
normalizeTrace e = Debug.Trace.trace (show e) $ normalize e
--normalizeTrace e = normalize e

-- Arrow, CCA, and skew-mondoidal category laws (not yet all of them):
normalize :: AExp -> AExp
normalize (Arr f :>>> Arr g) = Arr (g `o` f)
normalize (First (Arr f)) = ArrFirst f
normalize (Second (Arr f)) = ArrSecond f

normalize (Arr f :>>> LoopD i g) = LoopD i (g `o` (f `crossE` idE))
normalize (LoopD i f :>>> Arr g) = LoopD i ((g `crossE` idE) `o` f)
normalize (LoopD i f :>>> LoopD j g) = LoopD (tupE [i,j])
  (assocE `o` juggleE `o` (g `crossE` idE) `o` juggleE `o` (f `crossE` idE) `o` assocE')
normalize (Loop (LoopD i f)) = LoopD i (traceE (juggleE `o` f `o` juggleE))
normalize (First (LoopD i f)) = LoopD i (juggleE `o` (f `crossE` idE) `o` juggleE)
normalize (Delay i) = LoopD i swapE
-- Choice:
normalize (Lft (Arr f)) = Arr (lftE f)
normalize (Lft (LoopD i f)) = LoopD i (untagE `o` lftE f `o` tagE)

normalize (Loop (Arr f)) = Arr (traceE f) -- Not in original CCA. 2015-TB Added by TOM: for rec?
normalize (Loop (ArrM f)) = ArrM (traceE f) -- Not in original CCA. 2015-TB Added by TOM: for rec?

-- Laws for effectful ArrM's
normalize (Arr f :>>> ArrM g) = ArrM [| $g . $f |]
normalize (ArrM f :>>> Arr g) = ArrM [| liftM $g . $f |]
normalize (First (ArrM f)) = ArrM ( f `crossME` [|return|] )
normalize (Second (ArrM f)) = ArrM ( [|return|] `crossME` f )
--normalize (LoopD i f :>>> ArrM g) = LoopD i ((g `crossME` [|return|]) `o` f) --TODO: check this, perhaps need a LoopDM?

-- | Category
normalize (f :>>> Id) = f
normalize (Id :>>> f) = f

normalize (Id :*** f) = Second f
normalize (f :*** Id) = First f
normalize (First Id) = Id
normalize (Second Id) = Id
normalize (Lft Id) = Id

-- Cartesian
normalize (Diag :>>> Fst) = Id
normalize (Diag :>>> Snd) = Id
normalize (Diag :>>> (f :*** g) ) = f :&&& g
normalize ((Fst :>>> f) :&&& (Snd :>>> g)) = f :*** g
normalize ((Snd :>>> f) :&&& (Fst :>>> g)) = g :*** f
normalize ((f :&&& g) :>>> Snd) = g
normalize ((f :&&& g) :>>> Fst) = f
normalize ((f :&&& g) :>>> Swap) = g :&&& f
normalize (Id :&&& g) = Diag :>>> Second g
normalize (f :&&& Id) = Diag :>>> First f


-- | Associative. Probably not handy yet
{-normalize ( Second Disassociate :>>> Disassociate :>>> First Disassociate ) = Disassociate :>>> Disassociate
normalize ( First Associate :>>> Associate :>>> Second Associate ) = Associate :>>> Associate
normalize ( First Swap :>>> Associate :>>> Second Swap) = Associate :>>> Swap :>>> Associate
normalize ( Second Swap :>>> Associate :>>> First Swap) = Associate :>>> Swap :>>> Associate
---}

-- Braided
normalize (Diag :>>> ArrM f) = ArrM ( [| dupE . $f |])
normalize (Swap :>>> Swap) = Id
normalize (Diag :>>> Swap) = Diag
-- Never a problem combining Diag with Arr, no rules have Diag on the right.
normalize (Diag :>>> Arr f) = Arr ( f `o` dupE)

normalize ((Diag :>>> ArrFirst f) :>>> Swap) = Diag :>>> ArrSecond f
normalize ((Diag :>>> ArrSecond f) :>>> Swap) = Diag :>>> ArrFirst f
normalize ((Diag :>>> First f) :>>> Swap) = Diag :>>> Second f
normalize ((Diag :>>> Second f) :>>> Swap) = Diag :>>> First f
normalize (ArrFirst f :>>> Swap) = ArrSecond f
normalize (ArrSecond f :>>> Swap) = ArrFirst f
normalize (First f :>>> Swap) = Second f
normalize (Second f :>>> Swap) = First f

-- Association of >>>. Not sure if needed or helpful.
normalize (f :>>> (g :>>> h)) = (f :>>> g) :>>> h -- Added by TOM
normalize ((f :>>> g) :>>> h) = (f :>>> g) :>>> h -- Added by TOM
normalize e = e

-- | Round 2 to remove residual Arr's from first/second usage
normalizeA :: AExp -> AExp
-- | ASSUMPTION: We presume that pure actions are fairly cheap to perform, thus not much to gain by *** or &&&
normalizeA (Arr f :*** Arr g) = Arr $ f `crossE` g
normalizeA (ArrM f :*** Arr g) = ArrM $ f `crossME` [| return . $g |]
normalizeA (Arr f :*** ArrM g) = ArrM $ [| return . $f |]  `crossME` g

normalizeA (Arr f :&&& Arr g) = Arr $ (f `crossE` g) `o` dupE
normalizeA (ArrM f :&&& Arr g) = ArrM $ (f `crossME` [| return . $g |]) `o` dupE
normalizeA (Arr f :&&& ArrM g) = ArrM $ ([| return . $f |]  `crossME` g) `o` dupE
normalizeA (ArrFirst f) = Arr (f `crossE` idE)
normalizeA (ArrSecond f) = Arr (idE `crossE` f)
normalizeA (f :>>> (g :>>> h)) = (f :>>> g) :>>> h -- Added by TOM
normalizeA ((f :>>> g) :>>> h) = (f :>>> g) :>>> h -- Added by TOM
--normalizeA Id = Arr idE
normalizeA Diag = Arr dupE
normalizeA Swap = Arr swapE
normalizeA Fst = Arr [|fst|]
normalizeA Snd = Arr [|snd|]
normalizeA f = normalize f

-- | Used to take the function produced by normOpt and process a stream.
-- TODO: explain various arguments, state etc.
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

dup :: t -> (t, t)
dup x = (x, x)
swap :: (t1, t) -> (t, t1)
swap (x, y) = (y, x)
unassoc :: (t1, (t2, t)) -> ((t1, t2), t)
unassoc (x, (y, z)) = ((x, y), z)
assoc :: ((t, t1), t2) -> (t, (t1, t2))
assoc ((x, y), z) = (x, (y, z))
juggle :: ((t1, t), t2) -> ((t1, t2), t)
juggle ((x, y), z) = ((x, z), y)
trace :: ((t1, t2) -> (t, t2)) -> t1 -> t -- pure looping
trace f x = let (y, z) = f (x, z) in y

cross :: (t -> t2) -> (t1 -> t3) -> (t, t1) -> (t2, t3)
cross f g (x, y) = (f x, g y)

--bimap :: r a b -> s c d -> t (p a c) (p b d)
--Bifunctor (,) (->) (->) (->)
-- is this bimap?
crossM :: Monad m => (t -> m t2) -> (t1 -> m t3) -> (t, t1) -> m (t2,t3)
crossM f g (x, y) = do
    a <- f x
    b <- g y
    return (a,b)

mirror :: Either b a -> Either a b
mirror (Left x) = Right x
mirror (Right y) = Left y
untag :: Either t t -> t
untag (Left x) = x
untag (Right y) = y
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
f `o` g = appE (appE [|(.)|] f) g
crossE :: ExpQ -> ExpQ -> ExpQ
f `crossE` g = appE (appE [|cross|] f) g

crossME :: ExpQ -> ExpQ -> ExpQ
f `crossME` g = appE (appE [|crossM|] f) g

idE,dupE,swapE,assocE,assocE',juggleE,tagE,untagE :: ExpQ
idE = [|id|]
dupE = [|dup|]
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

simplify :: String -> String
simplify = unwords . map (unwords . map aux . words) . lines
  where aux (c:x) | not (isAlpha c) = c : aux x
        aux x = let (_, v) = break (=='.') x
                in if length v > 1 then aux (tail v)
                                   else x

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
