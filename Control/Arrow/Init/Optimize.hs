{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE CPP, TemplateHaskell, FlexibleInstances #-}
-- originally from CCA package: https://hackage.haskell.org/package/CCA-0.1.5.2
module Control.Arrow.Init.Optimize
  (norm, normOpt,fromAExp, normalize, normE,
   pprNorm, pprNormOpt, printCCA, ASyn(..),AExp(..),ArrowInit(..),
   cross, dup, swap, assoc, unassoc, juggle, trace, mirror, untag, tagT, untagT,
   swapE, dupE,lowerTH) where

import Control.Category
import Prelude hiding ((.), id, init)

import Control.Arrow
import Control.Arrow.Init
import Data.Char (isAlpha)
import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import qualified Language.Haskell.Exts.Syntax as E
import Data.Generics.Uniplate.Data


import qualified Data.Generics as G (everywhere, mkT)
-- Internal Representation
-- =======================

-- We use AExp to syntactically represent an arrow for normalization purposes. 

data AExp
  = Arr ExpQ
  | First AExp
  | AExp :>>> AExp

  | Expr ExpQ
  | Func
  | Effect ExpQ

  | AExp :*** AExp -- added to prevent premature optimization? or to allow it?

  | Loop AExp
  | LoopD ExpQ ExpQ -- loop with initialized feedback
  | Init ExpQ
  | Lft AExp

infixl 1 :>>>
infixl 1 :***

instance Show AExp where
    show (Arr _) = "Arr"
    show (First f) = "First " ++ show f
    show (Effect _) = "Effect"
    show (f :>>> g) = "(" ++ show f ++ " >>> " ++ show g ++ ")"
    show (f :*** g) = "[" ++ show f ++ " *** " ++ show g ++ "]"
    show (Loop f) = "Loop " ++ show f
    show (LoopD _ _) = "LoopD"
    show (Init _) = "Init"
instance Show (ASyn m a b) where
    show (AExp x) = show x

-- We use phantom types to make ASyn an Arrow.

newtype ASyn (m :: * -> * ) b c = AExp AExp

instance Category (ASyn m) where
    id = AExp (Arr [|\x -> x|])
    AExp g . AExp f = AExp (f :>>> g)
instance Arrow (ASyn m) where
    arr f = error "ASyn arr not implemented"
    first (AExp f) = AExp (First f)
    (AExp f) *** (AExp g) = AExp (f :*** g)
instance ArrowLoop (ASyn m) where
    loop (AExp f) = AExp (Loop f)
instance ArrowInit (ASyn m) where
    init i = error "ASyn init no implemented"
    init' f _ = AExp (Init f)
    arr' f _ = AExp (Arr f)
{-
--ArrowChoice only requires definition for 'left', but the default implementation
--for 'right' and '|||' uses arr so we need to redefine them using arr' here.
--'+++' is also redefined here for completeness.
instance Monad m => ArrowChoice (ASyn m) where
    left (AExp f) = AExp (Lft f)
    right f = arr' [| mirror |] mirror >>> left f >>> arr' [| mirror |] mirror
    f +++ g = left f >>> right g
    f ||| g = f +++ g >>> arr' [| untag |] untag
--}
-- Pretty printing AExp.

printCCA :: ASyn m t t1 -> IO ()
printCCA (AExp x) = printAExp x
printAExp :: AExp -> IO ()
printAExp x = runQ (fromAExp x) >>= putStrLn . simplify . pprint
simplify :: String -> String
simplify = unwords . map (unwords . map aux . words) . lines
  where aux (c:x) | not (isAlpha c) = c : aux x
        aux x = let (_, v) = break (=='.') x
                in if length v > 1 then aux (tail v)
                                   else x

-- Traversal over AExp is defined in terms of imap (intermediate map)
-- and everywhere.

type Traversal = AExp -> AExp
imap :: Traversal -> Traversal
imap h (First f) = First (h f)
imap h (f :>>> g) = h f :>>> h g
imap h (Loop f) = Loop (h f)
imap h (Lft f) = Lft (h f)
imap _ x = x

everywhere :: Traversal -> Traversal
everywhere h = h . imap (everywhere h)

-- Normalization
-- =============

-- norm is a TH function that normalizes a given CCA, e.g., $(norm e) will
-- give the CCNF of e.

norm :: AExp -> ExpQ         -- returns a generic ArrowInit arrow
norm e = fromAExp (normE e)
normE :: Traversal
normE = everywhere normalize

-- normOpt returns the pair of state and pure function as (i, f) from optimized
-- CCNF in the form loopD i (arr f).

normOpt :: ASyn m a b -> ExpQ      -- returns a pair of state and pure function (s, f)
normOpt (AExp e) =
  case normE e of
    LoopD i f -> tupE [i, f]
    Arr f     -> [| ( (), $(f) ) |]
    -- Effect f  -> [| ( (), $(f) ) |]
    g -> error $ "Can't optimize past: " ++ show g
    -- _         -> error $ "The given arrow can't be normalized to optimized CCNF."

-- pprNorm and pprNormOpt return the pretty printed normal forms as a
-- string.

pprNorm :: AExp -> Q Exp
pprNorm = ppr' . norm

pprNormOpt :: ASyn m a b -> Q Exp
pprNormOpt = ppr' . normOpt
ppr' :: Q Exp -> Q Exp
ppr' e = runQ (fmap toLet e) >>= litE . StringL . simplify . pprint

-- fromAExp converts AExp back to TH Exp structure.

fromAExp :: AExp -> ExpQ
fromAExp (Arr f) = appE [|arr|] f
fromAExp (First f) = appE [|first|] (fromAExp f)
fromAExp (f :>>> g) = infixE (Just (fromAExp f)) [|(>>>)|] (Just (fromAExp g))
fromAExp (Loop f) = appE [|loop|] (fromAExp f)
fromAExp (LoopD i f) = appE (appE [|loopD|] i) f
fromAExp (Init i) = appE [|init|] i
fromAExp (Lft f) = appE [|left|] (fromAExp f)
fromAExp (f :*** g) = infixE (Just (fromAExp f)) [|(***)|] (Just (fromAExp g))

fromAExp (Expr f) = fmap lowerTH f -- TOM added
lowerTH :: Exp -> Exp
lowerTH = rewrite arg
    where
        arg (VarE (Name (OccName "Arr") _)) = Just $ VarE (Name (OccName "arr") NameS)
        arg (VarE (Name (OccName ":>>>") _)) = Just $ VarE (Name (OccName ">>>") NameS)
        {-
        arg (AppE (E.Var (E.UnQual (E.Ident "arr"))) b) = Just $ arrFun b
        arg (E.App (E.Var (E.UnQual (E.Symbol "arr"))) b) = Just $ arrFun b
        arg (E.App (E.Var (E.Qual _ (E.Symbol "arr"))) b) = Just $ arrFun b
        arg (E.App (E.Var (E.Qual _ (E.Ident "arr"))) b) = Just $ arrFun b
        arg (E.App (E.Var (E.UnQual (E.Ident "init"))) b) = Just $ app (var (name "Init")) b
        arg (E.App (E.Var (E.UnQual (E.Symbol "init"))) b) = Just $ app (var (name "Init")) b
        arg (E.App (E.Var (E.Qual _ (E.Symbol "init"))) b) = Just $ app (var (name "Init")) b
        arg (E.App (E.Var (E.Qual _ (E.Ident "init"))) b) = Just $ app (var (name "Init")) b
        arg (E.Var (E.UnQual (E.Ident "returnA"))) = Just $ arrFun (var $ name "id")
        arg (E.Var (E.UnQual (E.Symbol "returnA"))) = Just $ arrFun (var $ name "id")
        arg (E.Var (E.Qual _ (E.Ident "returnA"))) = Just $ arrFun (var $ name "id")
        arg (E.Var (E.Qual _ (E.Symbol "returnA"))) = Just $ arrFun (var $ name "id")
        arg (E.InfixApp leftExp (E.QVarOp (E.UnQual (E.Symbol ">>>"))) rightExp ) = Just $ infixApp leftExp (op $ name ":>>>") rightExp
        --arg (E.InfixApp leftExp (E.QVarOp (E.UnQual (E.Symbol "<<<"))) rightExp ) = Just $ infixApp rightExp (op $ name ":>>>") leftExp
        --arg (E.InfixApp leftExp (E.QVarOp (E.UnQual (E.Symbol "***"))) rightExp ) = Just $ infixApp leftExp (op $ name ":***") rightExp
        -}
        arg _ = Nothing

-- CCNF
-- ====

-- Arrow laws:

normalize :: AExp -> AExp
normalize (Arr f :>>> Arr g) = Arr (g `o` f)
normalize (First (Arr f)) = Arr (f `crossE` idE)
normalize (Arr f :>>> LoopD i g) = LoopD i (g `o` (f `crossE` idE))
normalize (LoopD i f :>>> Arr g) = LoopD i ((g `crossE` idE) `o` f)
normalize (LoopD i f :>>> LoopD j g) = LoopD (tupE [i,j])
  (assocE `o` juggleE `o` (g `crossE` idE) `o` juggleE `o` (f `crossE` idE) `o` assocE')
normalize (Loop (LoopD i f)) = LoopD i (traceE (juggleE `o` f `o` juggleE))
normalize (First (LoopD i f)) = LoopD i (juggleE `o` (f `crossE` idE) `o` juggleE)
normalize (Init i) = LoopD i swapE

normalize (Arr f :>>> Expr g) = Arr (g `o` f) -- TOM added
normalize (First (Expr (fmap lowerTH -> f))) = Arr (f `crossE` idE)

-- Choice:

normalize (Lft (Arr f)) = Arr (lftE f)
normalize (Lft (LoopD i f)) = LoopD i (untagE `o` lftE f `o` tagE)

-- All the other cases are unchanged.

normalize e = e

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
cross :: (t -> t2) -> (t1 -> t3) -> (t, t1) -> (t2, t3)
cross f g (x, y) = (f x, g y)
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

