{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE LambdaCase #-}
{- |
Module      :  Control.Arrow.TH
Description :  Arrow notation QuasiQuoter
Copyright   :  (c) 2015 Thomas Bereknyei
License     :  BSD3
Maintainer  :  Thomas Bereknyei <tomberek@gmail.com>
Stability   :  unstable
Portability :  TemplateHaskell,QuasiQuotes,ViewPatterns

-}
module Control.Arrow.CCA.Free (
    arrow2,printCCA,into,buildA,
    cleanNames,parseMode,arrFixer,fixity,
    AExp(..),ASyn(..),fromAExp,findM,
    areExpAEq',eqM,simplify,rules,category,C.Dict(..),fromASyn,
    norm
    ) where
import qualified Language.Haskell.Exts as E
import Unsafe.Coerce

import Control.Category
import Language.Haskell.Meta
import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Quote
import Language.Haskell.Meta.Utils
import Language.Haskell.Meta.Parse
import Control.Arrow.CCA -- no Q or with Q?
import Control.Arrow hiding ((&&&),(***),first,second)
import qualified Control.Category as Q
import Data.List (filter,partition,foldr,mapAccumL,findIndices,elemIndex,(\\),(!!),delete,nub,find)
--import Data.Graph

--import Data.IntMap hiding (map)
import Data.Function(on)
import Language.Haskell.TH.Utilities
--import qualified Data.Set as Set
import Data.Maybe
import qualified Debug.Trace
import Control.Lens hiding (Bifunctor)
import Control.Applicative
import Control.Arrow.TH.Structural

import qualified Control.Lens as L
import Control.Category.Associative
import Control.Category.Structural
import Control.Category.Monoidal
import Control.Category.Cartesian
import Control.Categorical.Bifunctor
import           Control.Category
import           Prelude             hiding (id, (.),fst,snd)
import           Control.Arrow hiding (first,second,(***),(&&&))
import qualified Control.Arrow as A
import Control.Monad(liftM,(>=>),(>>),msum,mplus)
import Data.Data (Data(..))
import qualified Data.Generics       as G (everywhere,everywhereM,mkT)
import           Data.Char           (isAlpha)
import Data.Generics.Aliases
--import Control.CCA.Normalize
import Data.Typeable
import Data.Data
import qualified Data.Constraint as C
import Control.Monad.Trans.Maybe

parseMode = E.defaultParseMode{E.extensions=[E.EnableExtension E.Arrows],E.fixities=Just (E.baseFixities)}

arrow2 :: QuasiQuoter
arrow2 = QuasiQuoter {
  quoteExp = \input -> case E.parseExpWithMode parseMode input of
      E.ParseOk result -> do
          res <- buildA result
          --res2 <- L.rewriteM (reifyAlpha' ruleSet) res
          --reportWarning $ show res
          let res' = TExp res
          --res2 <- (dataToTExpQ' (const Nothing `extQ` d) (res'))
          --reportWarning $ show res4
          return $ res
      E.ParseFailed l err -> error $ "arrow QuasiQuoter: " ++ show l ++ " " ++ show err
  , quotePat = error "cannot be patterns."
  , quoteDec = \input -> case E.parseDeclWithMode parseMode input of
      E.ParseOk result -> undefined
      E.ParseFailed l err -> error $ "arrow QuasiQuoter in Decl: " ++ show l ++ " " ++ show err
  , quoteType = error "cannot be types."
    }
    where parseMode = E.defaultParseMode{E.extensions=[E.EnableExtension E.Arrows],E.fixities=Just (E.baseFixities)}

--category :: C.Dict (con a) -> [(con a => TExp (a b c) -> (Q (TExp (a b c))))] -> QuasiQuoter
category :: [Exp -> Q (Maybe Exp)] -> QuasiQuoter
category rules = QuasiQuoter {
  quoteExp = \input -> case E.parseExpWithMode parseMode input of
      E.ParseOk result -> do
          res <- buildA result
          let
              rules' exp = (runMaybeT . msum $ ( MaybeT . fmap cleanNames . (fmap.fmap) (transform fixity) . flip ($) exp) <$> rules)
              res2 = transform fixity $ cleanNames res
          res3 <- rewriteM (rules' . transform fixity) res2
          reportWarning $ pprint res3
          return res3 >>= arrFixer
      E.ParseFailed l err -> error $ "arrow QuasiQuoter: " ++ show l ++ " " ++ show err
  , quotePat = error "cannot be patterns."
  , quoteDec = error "category: cannot by dec"
  , quoteType = error "cannot be types."
    }
     where parseMode = E.defaultParseMode{E.extensions=[E.EnableExtension E.Arrows],E.fixities=Just (E.baseFixities)}

-- | Replaces expressions of `arr`, `arrM`, `delay`, and `returnA` with
-- the versions that have their arguments lifted to TH.
arrFixer :: Exp -> ExpQ
arrFixer = rewriteM arg
    where
        arg (AppE (VarE (Name (OccName "arr") _)) e) =
            fmap Just [| arr' (returnQ $(lift e)) $(returnQ e) |]
        arg (AppE (VarE (Name (OccName "arrM") _)) e) =
            fmap Just [| arrM' (returnQ $(lift e)) $(returnQ e) |]
        arg (AppE (VarE (Name (OccName "delay") _)) e) =
            fmap Just [| delay' (returnQ $(lift e)) $(returnQ e) |]
        arg (VarE (Name (OccName "returnA") _)) =
            fmap Just [| arr' (returnQ $([| Q.id |] >>= lift)) Q.id |]
        arg (AppE (ConE (Name (OccName "Lift") _)) e) =   -- Huh?
            fmap Just $ returnQ e
        arg (AppE (VarE (Name (OccName "terminate") _)) e) =
            fmap Just [| terminate' (returnQ $(lift e)) $(returnQ e) |]
        arg _ = return Nothing

arrFixer' :: Exp -> ExpQ
arrFixer' = rewriteM arg
    where
        arg (AppE (VarE (Name (OccName "arr") _)) e) =
            fmap Just [| arr' ($(lift e)) $(returnQ e) |]
        arg (AppE (VarE (Name (OccName "arrM") _)) e) =
            fmap Just [| arrM' ($(lift e)) $(returnQ e) |]
        arg (AppE (VarE (Name (OccName "delay") _)) e) =
            fmap Just [| delay' ($(lift e)) $(returnQ e) |]
        arg (VarE (Name (OccName "returnA") _)) =
            fmap Just [| arr' ($([| Q.id |] >>= lift)) Q.id |]
        arg (AppE (ConE (Name (OccName "Lift") _)) e) =   -- Huh?
            fmap Just $ returnQ e
        arg (AppE (VarE (Name (OccName "terminate") _)) e) =
            fmap Just [| terminate' ($(lift e)) $(returnQ e) |]
        arg _ = return Nothing

buildA :: E.Exp -> ExpQ
buildA (E.Proc _ pat exp) = buildB pat exp
buildA exp = return $ toExp exp

pattern P p <- (toPat -> p)
pattern E e <- (toExp -> e)
pattern R r <- (return -> r)

buildB :: E.Pat -> E.Exp -> ExpQ
buildB pat (E.Do exps) = do
    --reportWarning "un-split proc pattern"
    snd $ head final
    where rest = buildC (init exps) [(pat,[|id|])]
          final = buildC [last exps] rest
buildB pat s@(E.LeftArrApp _ _)
           -- | promote (toPat p) == (toExp e) = [| $arrow |] -- Id arrow law
           | otherwise = [| $(snd $ buildD' (E.Qualifier s) [(pat,[|id|])] )|]
buildB a b = error $ "Not supported: " ++ show (a,b)

buildC :: [E.Stmt] -> [(E.Pat,ExpQ)] -> [(E.Pat,ExpQ)]
buildC [] exps = exps
buildC stmts exps = if null newExps then exps else buildC rest (newExps ++ exps)
    where (goals,rest) = Data.List.partition (all (flip elem $ freeVars $ fst <$> exps) . freeVars) stmts
          sources :: [(E.Stmt,[(E.Pat,ExpQ)])] -- statements that can be built with their dependencies
          sources = zip goals $ sourceGetter <$> goals
          sourceGetter :: E.Stmt -> [(E.Pat,ExpQ)]
          sourceGetter (freeVars -> s) = Data.List.filter (any (flip elem s) . freeVars . fst) exps
          newExps = map (uncurry buildD') sources

(*:*) :: ExpQ -> ExpQ -> ExpQ
expr1 *:* expr2 = infixE (Just expr1) (varE $ mkName "***") (Just expr2)
(&:&) :: ExpQ -> ExpQ -> ExpQ
expr1 &:& expr2 = infixE (Just expr1) (varE $ mkName "&&&") (Just expr2)

buildD' :: E.Stmt -> [(E.Pat,ExpQ)] -> (E.Pat,ExpQ)
buildD' stmt s = (origp,[| $fixedTuple  >>> $(returnQ $ toExp arrow) |])
    where
          fixedTuple = fixTuple (snd <$> s) (tuplizer E.PWildCard (E.PTuple E.Boxed) ( fst <$> s)) exp
          (arrow,exp,origp) = case stmt of
                               (E.Qualifier (E.LeftArrApp arrows f)) -> (arrows,f,E.PWildCard)
                               (E.Generator _ p (E.LeftArrApp arrows f)) -> (arrows,f,p)
                               (E.LetStmt (E.BDecls [E.PatBind _ p _ (E.UnGuardedRhs f) _])) -> (eId,f,p)
                               a -> error $ show a
eId = E.Var (E.UnQual $ E.Ident "id")

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
  | Lft AExp -- arrow choice
  | Lift ExpQ -- arrow lifted

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
  -- Monoidal
  | Idr
  | Idl
  | Coidl
  | Coidr
  | Terminate ExpQ
  --deriving (Typeable,Data)
  {- Closed, not needed
  | Apply -- (f,a) = f a   arr (\(f,a)->f a)
  | Curry
  | Uncurry
  -}
--instance L.Plated AExp

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
          expf (InfixE (Just (ParensE l)) op (Just r)) = InfixE (Just l) op (Just r)
          expf (InfixE (Just l) op (Just (ParensE r))) = InfixE (Just l) op (Just r)
          expf e = e
fixity' :: Data a => a -> a
fixity' = G.everywhere (G.mkT expf)
    where expf (InfixE (Just l) op (Just r)) = UInfixE l op r
          expf e = e

-- | Used to measure progress for normalization using rewriteM
eqM :: AExp -> AExp -> Q Bool
eqM (Arr f) (Arr g) = areExpAEq' f g
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
eqM (Lift f) (Lift g) = areExpAEq' f g
eqM Associate Associate = return True
eqM Disassociate Disassociate = return True
eqM Swap Swap = return True
eqM Coidl Coidl = return True
eqM Coidr Coidr = return True
eqM Idr Idr = return True
eqM Idl Idl = return True
eqM (Terminate a) (Terminate b) = areExpAEq' a b
eqM _ _ = return False

instance Eq AExp where
    First f == First g = f==g
    Second f == Second g = f==g
    (f :>>> g) == (h :>>> i) = f == h && g == i
    (f :*** g) == (h :*** i) = f == h && g == i
    (f :&&& g) == (h :&&& i) = f == h && g == i
    (Loop f) == (Loop g) = f == g
    Id == Id = True
    Diag == Diag = True
    Fst == Fst = True
    Snd == Snd = True
    Associate == Associate = True
    Disassociate == Disassociate = True
    Swap == Swap = True
    Coidl == Coidl = True
    Coidr == Coidr = True
    Idl == Idl = True
    Idr == Idr = True
    _ == _ = False

infixr 1 :>>>
infixr 3 :***
infixr 3 :&&&
    

instance Show AExp where
    show Id = "Id"
    show Diag = "Diag"
    show Swap = "Swap"
    show Fst = "Fst"
    show Snd = "Snd"
    show Coidl = "Coidl"
    show Coidr = "Coidr"
    show Idr = "Idr"
    show Idl = "Idl"
    show Associate = "Associate"
    show Disassociate = "Disassociate"
    show (Arr _) = "Arr"
    show (First f) = "First " ++ show f
    show (Second f) = "Second " ++ show f
    show (ArrM _) = "ArrM"
    show (f :>>> g) = "(" ++ show f ++ " >>> " ++ show g ++ ")"
    show (f :*** g) = "[" ++ show f ++ " *** " ++ show g ++ "]"
    show (f :&&& g) = "[" ++ show f ++ " &&& " ++ show g ++ "]"
    show (Loop f) = "Loop " ++ show f
    show (LoopD _ _) = "LoopD"
    show (Delay _) = "Delay"
    show (Lft _) = "Lft"
    show (Lift _) = "Lift"
    show (Terminate _) = "Terminate"
instance Show (ASyn m a b) where
    show (AExp x) = show x

-- We use phantom types to make ASyn an Arrow.
newtype ASyn (m :: * -> *) b c = AExp {untype::AExp}

instance Category (ASyn m) where
    id = AExp Id
    AExp g . AExp f = AExp (f :>>> g)
instance QFunctor p (ASyn m) where
    second (AExp f) = AExp (Second f)
instance PFunctor p (ASyn m) where
    first (AExp f) = AExp (First f)
instance Bifunctor p (ASyn m) where
    AExp f *** AExp g = AExp $ f :*** g
instance Contract p (ASyn m) where
    AExp f &&& AExp g = AExp $ f :&&& g
    diag = AExp Diag
instance HasLeftIdentity () p (ASyn m) where
    coidl = AExp Coidl
    idl = AExp Idl
instance HasRightIdentity () p (ASyn m) where
    coidr = AExp Coidr
    idr = AExp Idr
instance HasIdentity () (,) (ASyn m)
instance HasTerminal (ASyn m) where
    terminate _ = error "ASyn terminate not implemented"
    terminate' a _ = AExp $ Terminate a
instance Weaken p (ASyn m) where
    fst = AExp Fst
    snd = AExp Snd
instance Symmetric p (ASyn m) where
    swap = AExp Swap
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
    --right f = arr' [| mirror |] mirror >>> left f >>> arr' [| mirror |] mirror
    right f = arr mirror >>> left f >>> arr mirror
    f +++ g = left f >>> right g
    --f ||| g = f +++ g >>> arr' [| untag |] untag
    f ||| g = f +++ g >>> arr untag
mirror :: Either b a -> Either a b
mirror (Left x) = Right x
mirror (Right y) = Left y
untag :: Either t t -> t
untag (Left x) = x
untag (Right y) = y

-- Pretty printing AExp.
printCCA :: ASyn m t t1 -> IO ()
printCCA (AExp x) = runQ (fromAExp x) >>= putStrLn . simplify . pprint -- simplify . pprint

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
        , ([| \a -> () |],Terminate $ tupE [])
        , ([| \a -> ((),()) |],Terminate (tupE []) :*** Terminate (tupE []))
        , ([| \a -> (a,a)|],Diag)
        , ([| \(a,b) -> a|],Fst)
        , ([| arr fst |],Fst)
        , ([| \(a,b) -> b|],Snd)
        , ([| arr snd |],Snd)
        , ([| \(a,b) -> (b,a)|],Swap)
        , ([| arr swap |],Swap)
        , ([| arr (\(a,b) -> (b,a))|],Swap)
        , ([| \(a,(b,c)) -> ((a,b),c)|],Disassociate)
        , ([| \((a,b),c) -> (a,(b,c))|],Associate) -- so far only first levels
        -- experimental. can this be automated?
        , ([| \(a,b) -> (a,a) |],Fst :>>> Diag)
        , ([| \(a,b) -> (b,b) |],Snd :>>> Diag)
        , ([| \((a,b),(c,d)) -> (a,c) |],Fst :*** Fst)
        , ([| \((a,b),(c,d)) -> (a,d) |],Fst :*** Snd)
        , ([| \((a,b),(c,d)) -> (b,c) |],Snd :*** Fst)
        , ([| \((a,b),(c,d)) -> (b,d) |],Snd :*** Snd)
        , ([| \((a,b),(c,d)) -> (c,a) |],Fst :*** Fst :>>> Swap)
        , ([| \((a,b),(c,d)) -> (d,a) |],Fst :*** Snd :>>> Swap)
        , ([| \((a,b),(c,d)) -> (c,b) |],Snd :*** Fst :>>> Swap)
        , ([| \((a,b),(c,d)) -> (d,b) |],Snd :*** Snd :>>> Swap)
        ]

-- | Monadic Find, coppied from another library (sorry, forgot which)
findM :: Monad m => (a -> m (Maybe t)) -> [a] -> m (Maybe t)
findM f = Data.List.foldr test (return Nothing)
    where test x m = do
              curr <- f x
              maybe m (const $ return curr) curr

-- | fromAExp converts AExp back to TH Exp structure.
fromAExp :: AExp -> ExpQ

fromAExp Id = [|id|] -- Categorical constructors should not be around after second stage
fromAExp Diag = [| diag |]
fromAExp Fst = [| fst |]
fromAExp Snd = [| snd |]
fromAExp Associate = [| arr (\((a,b),c)->(a,(b,c))) |]
fromAExp Disassociate = [| arr (\(a,(b,c))->((a,b),c)) |]
fromAExp Swap = [| swap |]
fromAExp Coidr = [| coidr |]
fromAExp Coidl = [| coidl |]
fromAExp Idl = [| idl |]
fromAExp Idr = [| idr |]
fromAExp (Terminate a) = [| terminate $a |]

-- Should not be arround after second rewrite pass:
fromAExp (Arr f) = [|arr $f |]
fromAExp (First f) = appE [|first|] (fromAExp f)
fromAExp (Second f) = appE [|second|] (fromAExp f)
fromAExp (f :>>> g) = infixE (Just (fromAExp f)) [|(>>>)|] (Just (fromAExp g))
fromAExp (Loop f) = appE [|loop|] (fromAExp f)
fromAExp (LoopD i f) = [|loopD $i $f |]
fromAExp (ArrM i) = [|arrM $i |]
fromAExp (Delay i) = [|delay $i |]
fromAExp (Lft f) = appE [|left|] (fromAExp f)
fromAExp (Lift f) = f
fromAExp (f :*** g) = infixE (Just (fromAExp f)) [|(***)|] (Just (fromAExp g)) -- Not in original CCA. 2015-TB
fromAExp (f :&&& g) = infixE (Just (fromAExp f)) [|(&&&)|] (Just (fromAExp g)) -- Not in original CCA. 2015-TB

fromASyn (AExp a) = fromAExp a


-- | norm is a TH function that normalizes a given CCA, e.g., $(norm e) will
-- give the CCNF of e.
norm :: ASyn t t1 t2 -> Q Exp
norm (AExp e) = fromAExp (normalize e) >>= arrFixer

{-
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
                              -}

-- normOpt returns the pair of state and pure function as (s, f) from optimized
-- CCNF in the form loopD i (arr f).
normOpt :: ASyn m a b -> ExpQ
normOpt (AExp e) = do
    let e' = normalize e
    case e' of
      LoopD i f -> tupE [i,f]
      Arr f     -> [| ( (), $f ) |]
      ArrM f  -> [| ( (), $f ) |]
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
normalize (f :>>> Terminate g) = Terminate g
normalize (f :>>> (Terminate g :*** Terminate h)) = Terminate g :*** Terminate h
normalize (f :>>> (Terminate g :&&& Terminate h)) = Terminate g :&&& Terminate h

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
normalize (Fst :&&& Snd) = Id
normalize (Snd :&&& Fst) = Swap
normalize ((Fst :>>> f) :&&& Snd) = f :*** Id
normalize ((Snd :>>> f) :&&& Fst) = Swap :>>> f :*** Id
normalize (Fst :&&& (Snd :>>> f)) = Id :*** f
normalize (Snd :&&& (Fst :>>> f)) = Swap :>>> Id :*** f
normalize (Id :&&& Id) = Diag
normalize ((f :&&& g) :>>> Swap) = g :&&& f
normalize (Id :&&& g) = Diag :>>> Second g
normalize (f :&&& Id) = Diag :>>> First f
normalize w@((x :>>> f) :&&& (y :>>> g)) | x ==y = x :>>> (f :&&& g)
                                         | otherwise = w
normalize w@(x :&&& (y :>>> g)) | x ==y = x :>>> (Id :&&& g)
                                | otherwise = w
normalize w@((x :>>> f) :&&& y) | x ==y = x :>>> (f :&&& Id)
                                | otherwise = w

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
normalize (Swap :>>> First f) = Second f :>>> Swap
normalize (Swap :>>> Second f) = First f :>>> Swap
{-
normalize (First f :>>> Swap) = Swap :>>> Second f
normalize (Second f :>>> Swap) = Swap :>>> First f
-}

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


simplify :: String -> String
simplify = unwords . map (unwords . map aux . words) . lines
  where aux (c:x) | not (isAlpha c) = c : aux x
        aux x = let (_, v) = break (=='.') x
                in if length v > 1 then aux (tail v)
                                   else x
