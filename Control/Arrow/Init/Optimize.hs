{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}
{- |
Module      :  Control.Arrow.Init.Optimize
Description :  Optimize ArrowInit Instances
Copyright   :  (c) 2015 Thomas Bereknyei
License     :  BSD3
Maintainer  :  Thomas Bereknyei <tomberek@gmail.com>
Stability   :  unstable
Portability :  GADTs,TemplateHaskell,MultiParamTypesClasses

Originally from CCA package: <https://hackage.haskell.org/package/CCA-0.1.5.2>
-}
module Control.Arrow.Init.Optimize
    (normQ,norm, normOpt, normFixed, fromAExp, normalize, normE,
    runCCNF, nth', runIt,
    pprNorm, pprNormOpt, printCCA, ASyn(..),AExp(..),ArrowInit(..),
    --cross, dup, swap, assoc, unassoc, juggle, trace, mirror, untag, tagT, untagT,
    --swapE, dupE
    ) where

import           Control.Category
import           Prelude             hiding (id, init, (.))

import           Control.Arrow
import           Control.Arrow.Init
import           Control.Arrow.TH
import           Control.Monad --was just liftM
import           Control.Applicative
import qualified Data.Semifunctor.Braided as CCC
import           Data.Char           (isAlpha)
import           Language.Haskell.TH
import           Language.Haskell.TH.Utilities
import qualified Control.Lens as L
import qualified Debug.Trace
import Data.Data
import Data.Typeable

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
  | Loop AExp
  | LoopD ExpQ ExpQ -- loop with initialized feedback
  | Init ExpQ
  | Lft AExp

  | ArrList [AExp]
  | Id -- This and below added for Symetric Cartesian (not monoidal)
  | Diag
  | Fst
  | Snd
  | Associate
  | Disassociate
  | Swap
  | Second AExp
  -- Closed, not needed
  | Apply -- (f,a) = f a   arr (\(f,a)->f a)
  | Curry
  | Uncurry
  -- Monoidal, not needed
  | Idr
  | Idl
  | Coidl
  | Coidr

instance L.Plated AExp where
    plate f (First e) = First <$> f e
    plate f (Second e) = Second <$> f e
    plate f (a :>>> b) = (:>>>) <$> f a <*> f b
    plate f (a :*** b) = (:***) <$> f a <*> f b
    plate f (Loop e) = Loop <$> f e
    plate f (Lft e) = Lft <$> f e
    plate _ e = pure e

areExpAEq' f g = do
    f' <- f >>= return . fixity
    g' <- g >>= return . fixity
    case f' of
        UInfixE _ _ _ -> return False
        otherwise -> case g' of
            UInfixE _ _ _ -> return False
            otherwise -> expEqual f' g'

fixity :: Data a => a -> a
fixity = G.everywhere (G.mkT expf)
    where expf (UInfixE l o r) = InfixE (Just l) o (Just r)
          expf e = e

-- | Used to measure progres for normalization using rewriteM
eqM :: AExp -> AExp -> Q Bool
eqM (Arr f) (Arr g) = areExpAEq' f g
eqM (First f) (First g) = eqM f g
eqM (Second f) (Second g) = eqM f g
eqM (f :>>> g) (h :>>> i) = (&&) <$> (eqM f h) <*> (eqM g i)
eqM (ArrM f) (ArrM g) = areExpAEq' f g
eqM (f :*** g) (h :*** i) = (&&) <$> (eqM f h) <*> (eqM g i)
eqM (Loop f) (Loop g) = eqM f g
eqM (LoopD f g) (LoopD h i) = (&&) <$> (areExpAEq' f h) <*> (areExpAEq' g i)
eqM (Init f) (Init g) = areExpAEq' f g
eqM (Lft f) (Lft g) = eqM f g
eqM Id Id = return True
eqM Diag Diag = return True
eqM Fst Fst = return True
eqM Snd Snd = return True
eqM Associate Associate = return True
eqM Disassociate Disassociate = return True
eqM Swap Swap = return True
eqM (ArrList as) (ArrList bs) = liftM and $ zipWithM eqM as bs
eqM _ _ = return False

-- make sure this matches canonical
infixl 1 :>>>
infixl 1 :***

instance Show AExp where
    show Id = "Id"
    show Diag = "Diag"
    show Swap = "Swap"
    show (Arr _) = "Arr"
    show (First f) = "First " ++ show f
    show (ArrM _) = "ArrM"
    show (f :>>> g) = "(" ++ show f ++ " >>> " ++ show g ++ ")"
    show (f :*** g) = "[" ++ show f ++ " *** " ++ show g ++ "]"
    show (Loop f) = "Loop " ++ show f
    show (LoopD _ _) = "LoopD"
    show (Init _) = "Init"
    show (Lft _) = "Lft"
instance Show (ASyn m a b) where
    show (AExp x) = show x

-- We use phantom types to make ASyn an Arrow.
newtype ASyn (m :: * -> *) b c = AExp AExp

instance Category (ASyn m) where
    --id = AExp (Arr [| id |])
    id = AExp Id
    AExp g . AExp f = AExp (f :>>> g)
instance Arrow (ASyn m) where
    arr _ = error "ASyn arr not implemented"
    first (AExp f) = AExp (First f)
    --second (AExp f) = AExp (Swap :>>> First f :>>> Swap)
    second (AExp f) = AExp (Second f)
    (AExp f) *** (AExp g) = AExp (f :*** g)
    --(AExp f) *** (AExp g) = AExp (First f :>>> Arr swapE :>>> First g :>>> Arr swapE)
    --(AExp f) &&& (AExp g) = AExp (Arr dupE :>>> (First f :>>> Arr swapE :>>> First g :>>> Arr swapE))
    (AExp f) &&& (AExp g) = AExp (Diag :>>> (f :*** g))
instance ArrowLoop (ASyn m) where
    loop (AExp f) = AExp (Loop f)
instance ArrowInit (ASyn m) where
    arr' f _ = AExp (Arr f)
    init _ = error "ASyn init not implemented"
    init' f _ = AExp (Init f)
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
printCCA (AExp x) = printAExp x
printAExp :: AExp -> IO ()
printAExp x = runQ (fromAExp x) >>= putStrLn . simplify . pprint

-- Traversal over AExp is defined in terms of imap (intermediate map)
-- and everywhere.
type Traversal = AExp -> AExp
imap :: Traversal -> Traversal
imap h (First f) = First (h f)
imap h (f :>>> g) = h f :>>> h g
imap h (f :*** g) = h f :*** h g -- Added by TOM
imap h (Loop f) = Loop (h f)
imap h (Lft f) = Lft (h f)
imap _ x = x

everywhere :: Traversal -> Traversal
everywhere h = h . imap (everywhere h)

-- Normalization
-- =============

-- norm is a TH function that normalizes a given CCA, e.g., $(norm e) will
-- give the CCNF of e.
norm :: ASyn m a b -> ExpQ         -- returns a generic ArrowInit arrow
norm (AExp e) = fromAExp (normE e)
normE :: Traversal
normE = everywhere normalize

normQ (AExp e) = L.rewriteM normalizeJ e >>= fromAExp >>= arrFixer
normalizeQ = L.rewriteM normalizeJ
isId :: ExpQ -> Q Bool
isId expr = liftM or $ mapM ( ($) (areExpAEq' expr) ) [ [| \a -> a |]
                                                       , [| \(a,b) -> (a,b)|]
                                                       ]
rules = [ ([| \a -> a |],Id)
        , ([| id |],Id)
        , ([| \(a,b) -> (a,b)|],Id)
        , ([| \(a,(b,c)) -> (a,(b,c))|],Id)
        , ([| \((a,b),c) -> ((a,b),c)|],Id) -- so far only two levels
        , ([| \a -> (a,a)|],Diag)
        , ([| \(a,b) -> a|],Fst)
        , ([| fst |],Fst)
        , ([| \(a,b) -> b|],Snd)
        , ([| snd |],Snd)
        , ([| \(a,b) -> (b,a)|],Swap)
        , ([| \(a,(b,c)) -> ((a,b),c)|],Disassociate)
        , ([| \((a,b),c) -> (a,(b,c))|],Associate) -- so far only first levels
        ]
rewriteArr :: AExp -> Q (Maybe AExp)
rewriteArr (Arr e) = findM ( ($) (\(a,b) -> ifM (areExpAEq' e a) (return $ Just b) $ return Nothing)) rules

findM f = foldr test (return Nothing)
    where test x m = do
              curr <- f x
              case curr of
                  Just _  -> return curr
                  Nothing -> m

normalizeJ :: AExp -> Q (Maybe AExp)
normalizeJ (Arr e) = findM ( ($) (\(a,b) -> ifM (areExpAEq' e a) (return $ Just b) $ return Nothing)) rules
normalizeJ e = ifM (eqM e n) (return Nothing) (return $ Just n)
    where n = normalize e

normFixed :: ASyn m a b -> ExpQ
normFixed f = norm f >>= arrFixer
-- normOpt returns the pair of state and pure function as (i, f) from optimized
-- CCNF in the form loopD i (arr f).
normOpt :: ASyn m a b -> ExpQ      -- returns a pair of state and pure function (s, f)
normOpt (AExp e) = do
    e' <- normalizeQ e
    case e' of
      LoopD i f -> tupE [i, f]
      Arr f     -> [| ( (), $(f) ) |]
      ArrM f  -> [| ( (), $(f) ) |]
      g -> [| ( (), $(fromAExp g) ) |]
      --g -> error $ "Perhaps not causual? Can't optimize past: " ++ show g
      -- _         -> error $ "The given arrow can't be normalized to optimized CCNF."

-- | fromAExp converts AExp back to TH Exp structure.
fromAExp :: AExp -> ExpQ
--fromAExp (Swap :>>> First f :>>> Swap) = appE [|second|] (fromAExp f) --Added by TOM
--fromAExp (Diag :>>> First f :>>> Swap) = fromAExp $ Diag :>>> Second f --Added by TOM

fromAExp (Second f) = appE [|second|] (fromAExp f)
fromAExp Id = [|id|]
fromAExp Diag = [| arr dup |]
fromAExp Fst = [| arr fst |]
fromAExp Snd = [| arr snd |]
fromAExp Associate = [| arr (\((a,b),c)->(a,(b,c))) |]
fromAExp Disassociate = [| arr (\(a,(b,c))->((a,b),c)) |]
fromAExp Swap = [| arr swap |]

fromAExp (ArrList [Arr f]) = f --at least two things in ArrList
fromAExp (ArrList [Id]) = [|id|]
fromAExp (ArrList [Diag]) = [|dup|]
fromAExp (ArrList [Fst]) = [|fst|]
fromAExp (ArrList [Snd]) = [|snd|]
fromAExp (ArrList [Swap]) = [|swap|]
fromAExp (ArrList (f:rest)) = [| arr ( $(fromAExp $ ArrList rest) . $(fromAExp $ ArrList [f]) ) |]

fromAExp (Arr f) = appE [|arr|] f
fromAExp (First f) = appE [|first|] (fromAExp f)
fromAExp (f :>>> g) = infixE (Just (fromAExp f)) [|(>>>)|] (Just (fromAExp g))
fromAExp (Loop f) = appE [|loop|] (fromAExp f)
fromAExp (LoopD i f) = appE (appE [|loopD|] i) f
fromAExp (ArrM i) = appE [|arrM|] i
fromAExp (Init i) = appE [|init|] i
fromAExp (Lft f) = appE [|left|] (fromAExp f)
fromAExp (f :*** g) = infixE (Just (fromAExp f)) [|(***)|] (Just (fromAExp g)) -- Not in original CCA. 2015-TB
-- CCNF
-- ====

-- Arrow and CCA laws:
normalize :: AExp -> AExp
normalize (Arr f :>>> Arr g) = Arr (g `o` f)
normalize (First (Arr f)) = Arr (f `crossE` idE)
normalize (Second (Arr f)) = error "second found" --Arr (idE `crossE` f)
normalize (Arr f :>>> LoopD i g) = LoopD i (g `o` (f `crossE` idE))
normalize (LoopD i f :>>> Arr g) = LoopD i ((g `crossE` idE) `o` f)
normalize (LoopD i f :>>> LoopD j g) = LoopD (tupE [i,j])
  (assocE `o` juggleE `o` (g `crossE` idE) `o` juggleE `o` (f `crossE` idE) `o` assocE')
normalize (Loop (LoopD i f)) = LoopD i (traceE (juggleE `o` f `o` juggleE))
normalize (First (LoopD i f)) = LoopD i (juggleE `o` (f `crossE` idE) `o` juggleE)
normalize (Init i) = LoopD i swapE
normalize (Arr f :>>> ArrM g) = ArrM [| $g . $f |]
-- Choice:
normalize (Lft (Arr f)) = Arr (lftE f)
normalize (Lft (LoopD i f)) = LoopD i (untagE `o` lftE f `o` tagE)

normalize (ArrM f :>>> Arr g) = ArrM [| liftM $g . $f |]
normalize (Loop (Arr f)) = Arr (traceE f) -- Not in original CCA. 2015-TB Added by TOM
normalize (First (ArrM f)) = ArrM ( f `crossME` [|return|] ) -- Added by TOM

normalize (f :>>> Id) = f --Added by TOM
normalize (Id :>>> f) = f --Added by TOM
normalize (Id :*** f) = Second f --Added by TOM
normalize (f :*** Id) = First f --Added by TOM
normalize (First Id) = Id
normalize (Lft Id) = Id

normalize (Diag :>>> Fst) = Id
normalize (Diag :>>> Snd) = Id
normalize ( Diag :>>> (f :*** g) :>>> Snd) = g
normalize ( Diag :>>> (f :*** g) :>>> Fst) = f

normalize ( Second Disassociate :>>> Disassociate :>>> First Disassociate ) = Disassociate :>>> Disassociate
normalize ( First Associate :>>> Associate :>>> Second Associate ) = Associate :>>> Associate

normalize ( First Swap :>>> Associate :>>> Second Swap) = Associate :>>> Swap :>>> Associate
normalize ( Second Swap :>>> Associate :>>> First Swap) = Associate :>>> Swap :>>> Associate

normalize (Swap :>>> Swap) = Id
normalize (Diag :>>> Swap) = Diag

normalize (Diag :>>> First f :>>> Swap) = Diag :>>> Second f
normalize (Diag :>>> (First f :>>> Swap)) = Diag :>>> Second f
normalize (Diag :>>> Second f :>>> Swap) = Diag :>>> First f
normalize (Diag :>>> (Second f :>>> Swap)) = Diag :>>> First f
--normalize ((f :>>> g) :>>> h) = normE (f :>>> (g :>>> h)) -- Added by TOM
normalize (f :>>> (g :>>> h)) = (f :>>> g) :>>> h -- Added by TOM
--normalize (Second f) = Swap :>>> First f :>>> Swap
-- All the other cases are unchanged.
normalize (Diag :>>> Arr f) = ArrList [Diag,Arr f]
normalize (
normalize e = e

normalize2 (Diag :>>> Arr f) = Arr (f `o` dupE)
normalize2 (Arr f :>>> Diag) = Arr (dupE `o` f)
normalize2 (Arr f :>>> Swap) = Arr (swapE `o` f)
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
trace :: ((t1, t2) -> (t, t2)) -> t1 -> t
trace f x = let (y, z) = f (x, z) in y

{-# RULES
"cross_id_id" forall (f::forall a. a -> a) (g::forall b. b -> b) . cross f g = Debug.Trace.trace "cross_id_id fired" id
 #-}
{-# NOINLINE cross #-}
cross :: (t -> t2) -> (t1 -> t3) -> (t, t1) -> (t2, t3)
cross f g (x, y) = (f x, g y)

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
