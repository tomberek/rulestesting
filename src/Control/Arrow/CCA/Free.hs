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
    areExpAEq',eqM,simplify,rules,category,C.Dict(..)
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
import Control.Arrow.CCA.NoQ
import Control.Arrow hiding ((&&&),(***),first,second)
import qualified Control.Category as Q
import Data.List (filter,partition,foldr,mapAccumL,findIndices,elemIndex,(\\),(!!),delete,nub,find)
--import Data.Graph

--import Data.IntMap hiding (map)
import Data.Function(on)
import Language.Haskell.TH.Utilities
--import qualified Data.Set as Set
import Data.Maybe
import Debug.Trace
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
              rules' exp = (runMaybeT . msum $ ( MaybeT . fmap cleanNames . flip ($) exp) <$> rules)
              res2 = transform fixity' $ cleanNames res
          res3 <- rewriteM rules' res2
          --reportWarning $ show res3
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
          {-
buildB p (E.LeftArrApp (return . toExp -> arrow) e)
         -- | promote (toPat p) == (toExp e) = [| $arrow |] -- Id arrow law
         | otherwise = [| ( $(buildArrow p e) )  >>> ( $arrow )|]
          -}
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

-- Internal Representation
-- =======================
-- We use AExp to syntactically represent an arrow for normalization purposes.
data AExp
  = Arr Exp
  | First AExp
  | AExp :>>> AExp
  | ArrM Exp -- added to allow arrows with side effects
  | AExp :*** AExp -- added to prevent premature optimization? or to allow it?
  | AExp :&&& AExp -- added to prevent premature optimization? or to allow it?
  | Loop AExp       -- simple loop, needed for rec?
  | LoopD Exp Exp -- loop with delayed feedback
  | Delay Exp
  | Lft AExp -- arrow choice
  | Lift Exp -- arrow lifted

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
  | Terminate Exp
  deriving (Typeable,Data)
  {- Closed, not needed
  | Apply -- (f,a) = f a   arr (\(f,a)->f a)
  | Curry
  | Uncurry
  -}
instance L.Plated AExp

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
fixity' :: Data a => a -> a
fixity' = G.everywhere (G.mkT expf)
    where expf (InfixE (Just l) op (Just r)) = UInfixE l op r
          expf e = e

-- | Used to measure progress for normalization using rewriteM
eqM :: AExp -> AExp -> Q Bool
eqM (Arr f) (Arr g) = expEqual f g
eqM (First f) (First g) = eqM f g
eqM (Second f) (Second g) = eqM f g
eqM (f :>>> g) (h :>>> i) = (&&) <$> eqM f h <*> eqM g i
eqM (ArrM f) (ArrM g) = expEqual f g
eqM (f :*** g) (h :*** i) = (&&) <$> eqM f h <*> eqM g i
eqM (f :&&& g) (h :&&& i) = (&&) <$> eqM f h <*> eqM g i
eqM (Loop f) (Loop g) = eqM f g
eqM (LoopD f g) (LoopD h i) = (&&) <$> expEqual f h <*> expEqual g i
eqM (Delay f) (Delay g) = expEqual f g
eqM (Lft f) (Lft g) = eqM f g
eqM Id Id = return True
eqM Diag Diag = return True
eqM Fst Fst = return True
eqM Snd Snd = return True
eqM (Lift f) (Lift g) = expEqual f g
eqM Associate Associate = return True
eqM Disassociate Disassociate = return True
eqM Swap Swap = return True
eqM Coidl Coidl = return True
eqM Coidr Coidr = return True
eqM Idr Idr = return True
eqM Idl Idl = return True
eqM (Terminate a) (Terminate b) = expEqual a b
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
        , ([| \a -> () |],Terminate $ TupE [])
        , ([| \a -> ((),()) |],Terminate (TupE []) :*** Terminate (TupE []))
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
fromAExp (Terminate a) = [| terminate $(returnQ a) |]

-- Should not be arround after second rewrite pass:
fromAExp (Arr f) = appE [|arr|] (returnQ f)
fromAExp (First f) = appE [|first|] (fromAExp f)
fromAExp (Second f) = appE [|second|] (fromAExp f)
fromAExp (f :>>> g) = infixE (Just (fromAExp f)) [|(>>>)|] (Just (fromAExp g))
fromAExp (Loop f) = appE [|loop|] (fromAExp f)
fromAExp (LoopD i f) = appE (appE [|loopD|] (returnQ i)) (returnQ f)
fromAExp (ArrM i) = appE [|arrM|] (returnQ i)
fromAExp (Delay i) = appE [|delay|] (returnQ i)
fromAExp (Lft f) = appE [|left|] (fromAExp f)
fromAExp (Lift f) = returnQ f
fromAExp (f :*** g) = infixE (Just (fromAExp f)) [|(***)|] (Just (fromAExp g)) -- Not in original CCA. 2015-TB
fromAExp (f :&&& g) = infixE (Just (fromAExp f)) [|(&&&)|] (Just (fromAExp g)) -- Not in original CCA. 2015-TB

simplify :: String -> String
simplify = unwords . map (unwords . map aux . words) . lines
  where aux (c:x) | not (isAlpha c) = c : aux x
        aux x = let (_, v) = break (=='.') x
                in if length v > 1 then aux (tail v)
                                   else x
