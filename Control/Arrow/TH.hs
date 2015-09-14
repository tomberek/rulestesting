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
module Control.Arrow.TH (arrow,printCCA,reifyNames,reifyLaws,cca_laws,into,buildA, cleanNames,parseMode,arrFixer,fixity,AExp(..),ASyn(..),fromAExp,findM,areExpAEq',eqM,simplify,rules,reifyAlpha,category,C.Dict(..)) where
import qualified Language.Haskell.Exts as E
import Unsafe.Coerce

import Control.Category
import Language.Haskell.Meta
import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Quote
import Language.Haskell.Meta.Utils
import Language.Haskell.Meta.Parse
import Control.Arrow.CCA
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
import Control.Monad(liftM,(>=>),(>>))
import Data.Data (Data(..))
import qualified Data.Generics       as G (everywhere,everywhereM,mkT)
import           Data.Char           (isAlpha)
import Data.Generics.Aliases
--import Control.CCA.Normalize
import Data.Typeable
import qualified Data.Constraint as C

type ArrowExp = ExpQ
data NodeE =
    ProcN {_i::Int,_pat::E.Pat,_expr::E.Exp,_arrowE::ArrowExp}
    | StmtN {_i::Int,_pat::E.Pat,_expr::E.Exp,_arrowE::ArrowExp}
    | CmdN  {_i::Int,_pat::E.Pat,_expr::E.Exp,_arrowE::ArrowExp}
    | LetN {_i::Int,_pat::E.Pat,_expr::E.Exp,_arrowE::ArrowExp}
instance Show NodeE where
    show (ProcN i p e _) = "ProcN:" ++ show i ++ show p ++ show e
    show (StmtN i p e _) = "StmtN" ++ show i ++ show p ++ show e
    show (CmdN i p e _) = "CmdN" ++ show i ++ show p ++ show e
    show (LetN i p e _) = show i ++ show p ++ show e
makeLenses ''NodeE

reifyAlpha :: [(ExpQ,AExp)] -> AExp -> Q (Maybe AExp)
reifyAlpha ruleSet (Arr e) = findM (\(a,b) -> ifM (areExpAEq' e a) (return $ Just b) $ return Nothing) ruleSet
reifyAlpha _ e = return Nothing
reifyAlpha' :: [(ExpQ,ExpQ)] -> Exp -> Q (Maybe Exp)
reifyAlpha' ruleSet e = do
    --reportWarning $ show e
    findM (\(a,b) -> ifM (areExpAEq' (return e) a) (Just <$> b) $ return Nothing) ruleSet

reifyNames :: Exp -> Q (Maybe Exp)
reifyNames (VarE (Name occname NameS)) = return Nothing
reifyNames (VarE (Name occname _)) = return $ Just $ VarE (Name occname NameS)

--test (const (3::Int) -> s@(const "hi" -> t)) = _

reifyLaws' :: Exp -> Q (Maybe (TExp ((a,b) -> (a,b) )))
reifyLaws' =
    \case
        [rule| id *** id |]  -> into' [|| id ||]
        e -> return Nothing -- >> reportWarning (show e)



into' :: Q (TExp a) -> Q (Maybe (TExp a))
into' b = Just <$> b

reifyLaws :: Exp -> Q (Maybe Exp)
reifyLaws =
    \case
        [rule| id >>> id |]  -> intoA [| id |]
        [rule| id >>> x |]  -> intoA [| $x |]
        [rule| x >>> id |] -> intoA [| $x |]
        [rule| x &&& y |] | x_ == y_ -> intoA [| $x >>> diag |]
        [rule| first id |]   -> intoA [| id |]
        [rule| arr (\x -> y) |] | x_ == y_ -> intoA [| id |]
{-
          [rule| arr (\(x_,z_) -> y_) |] | x__ == y__ -> into [| fst |]
          [rule| arr (\(x_,z_) -> y_) |] | z__ == y__ -> into [| snd |]
          [rule| arr (\x_ -> (y_,z_)) |] | x__ == y__ && x__ == z__ -> into [| diag |]
          [rule| f_ >>> (g_ >>> h_) |]  -> into [| ($f_ >>> $g_) >>> $h_ |]
-}
        e -> return Nothing

reifyLawsRight =
    \case
    {-
          [rule| arr f_ >>> arr g_ |]  -> into [| arr ($g_ . $f_) |]
          [rule| (f_ >>> g_) >>> h_ |]  -> into [| $f_ >>> ($g_ >>> $h_) |]
          [rule| f_ >>> (g_ >>> h_) |]  -> return Nothing
    -}
          e -> reifyLaws e
s :: Q [Match] -> Q Exp
s a = do
    as <- a
    return $ LamCaseE as

cca_laws =  \case
          [rule| arr f >>> arr g |] -> intoA [| arr ($g . $f) |]
          [rule| fst |] -> intoA [| arr fst |]
          _ -> return Nothing

cca [rule| arr f >>> arr g |] = [| arr ( $g . $f) |]
cca [rule| x &&& y |] | x_ == y_ = [| $x >>> diag |]
intoA :: ExpQ -> Q (Maybe Exp)
intoA b = Just <$> b

ruleSet = [
        --([| arr (\a -> a) |],[| id |]) -- Category
        ([| Control.Arrow.arr (\(a,b) -> (a,b)) |],[| id *** id |]) -- Category
        --,([| arr (\(a,b) -> a) |],[| fst |]) -- Contract
        --,([| arr (\(a,b) -> b) |],[| snd |]) -- Contract
        ]

-- | A 'QuasiQuoter' that desugars proc-do notation and prepares for
-- CCA optimization via `arr'` and `delay'` usage.
arrow :: QuasiQuoter
arrow = QuasiQuoter {
  quoteExp = \input -> case E.parseExpWithMode parseMode input of
      E.ParseOk result -> do
          res <- buildA result
          --res2 <- L.rewriteM (reifyAlpha' ruleSet) res
          --reportWarning $ show res
          res3 <- L.rewriteM (reifyLaws) res
          res4 <- L.rewriteM (reifyLawsRight) res
          res5 <- return $ cleanNames res4 -- L.rewriteM (reifyNames) res4
          --reportWarning $ show res4
          arrFixer res5
      E.ParseFailed l err -> error $ "arrow QuasiQuoter: " ++ show l ++ " " ++ show err
  , quotePat = error "cannot be patterns."
  , quoteDec = \input -> case E.parseDeclWithMode parseMode input of
      E.ParseOk result -> undefined
      E.ParseFailed l err -> error $ "arrow QuasiQuoter in Decl: " ++ show l ++ " " ++ show err
  , quoteType = error "cannot be types."
    }
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
category :: [Exp -> Q Exp] -> QuasiQuoter
category rules = QuasiQuoter {
  quoteExp = \input -> case E.parseExpWithMode parseMode input of
      E.ParseOk result -> do
          res <- buildA result
          --res2 <- L.rewriteM (reifyAlpha' ruleSet) res
          --reportWarning $ show res
          --let [a,b] = unTypeRule s <$> rules
          --let ruleTs :: Data a => a -> Q a
           --     ruleTs = return `extM` a `extM` b
          let      r :: Data a => a -> Q a
                   r = foldl extM return rules
          res2 <- G.everywhereM r $ cleanNames $ fixity' res
          res3 <- G.everywhereM r $ cleanNames $ fixity' res2
          reportWarning $ show res3
          return res3 >>= arrFixer
      E.ParseFailed l err -> error $ "arrow QuasiQuoter: " ++ show l ++ " " ++ show err
  , quotePat = error "cannot be patterns."
  , quoteDec = error "category: cannot by dec"
  , quoteType = error "cannot be types."
    }
    where parseMode = E.defaultParseMode{E.extensions=[E.EnableExtension E.Arrows],E.fixities=Just (E.baseFixities)}


 {-
dataToTExpQ' :: ((Typeable b,Typeable c) => TExp (a b c) -> Maybe (Q (TExp (a b c)))) -> ((Typeable b,Typeable c) => TExp (a b c)) -> ((Typeable b,Typeable c)=> Q (TExp (a b c)))
dataToTExpQ' rules thing = dataToQa (returnQ . TExp . ConE)
                                    (returnQ . TExp . LitE)
                                    (foldl (\a b -> do
                                        TExp a' <- a
                                        TExp b' <- b
                                        return $ TExp $ AppE a' b')) (const Nothing `extQ` rules) thing
          -}


--cca2 ::Q (TExp (ArrowCCA a => ASyn m b c -> Q (TExp (a b c))))
cca2 = [| \case (untype -> Arr f :>>> Arr g) -> arr (f . g) |] -- >>= return . error . show


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


buildA :: E.Exp -> ExpQ
buildA (E.Proc _ pat exp) = buildB pat exp
buildA exp = return $ toExp exp

pattern P p <- (toPat -> p)
pattern E e <- (toExp -> e)
pattern R r <- (return -> r)

buildB :: E.Pat -> E.Exp -> ExpQ
buildB pat (E.Do exps) = snd $ head final
    where rest = buildC (init exps) [(pat,[|id|])]
          final = buildC [last exps] rest
buildB p (E.LeftArrApp (return . toExp -> arrow) e)
         -- | promote (toPat p) == (toExp e) = [| $arrow |] -- Id arrow law
         | otherwise = [| $(buildArrow p e) >>> $arrow |]
buildB a b = error $ "Not supported: " ++ show (a,b)

buildC :: [E.Stmt] -> [(E.Pat,ExpQ)] -> [(E.Pat,ExpQ)]
buildC [] exps = exps
buildC [stmt] [(pat,exp)] = [(pat',[| $exp >>> $exp' |])]
    where (pat',exp') = buildD pat stmt
buildC stmts exps = newExps ++ exps
    where (goals,rest) = Data.List.partition (all (flip elem $ freeVars $ fst <$> exps) . freeVars) stmts
          sources :: [(E.Stmt,[(E.Pat,ExpQ)])] -- statements that can be built with their dependencies
          sources = zip stmts $ sourceGetter <$> stmts
          sourceGetter :: E.Stmt -> [(E.Pat,ExpQ)]
          sourceGetter (freeVars -> s) = Data.List.filter (any (flip elem s) . freeVars . fst) exps
          newExps = map (uncurry buildD') sources

(*:*) :: ExpQ -> ExpQ -> ExpQ
expr1 *:* expr2 = uInfixE expr1 (varE $ mkName "***") expr2
(&:&) :: ExpQ -> ExpQ -> ExpQ
expr1 &:& expr2 = uInfixE expr1 (varE $ mkName "&&&") expr2

buildD' :: E.Stmt -> [(E.Pat,ExpQ)] -> (E.Pat,ExpQ)
buildD' stmt s = (out,[| $(foldl1 (&:&) (snd <$> s)) >>> $out2 |]) -- NOTE: Assumes &&& is available, fix with weakening laws?
    where (out,out2) = buildD (tuplizer E.PWildCard (E.PTuple E.Boxed) $ fst <$> s) stmt

buildD :: E.Pat -> E.Stmt -> (E.Pat,ExpQ)
buildD p (E.Qualifier      (E.LeftArrApp (return . toExp -> a) e )) = (E.PWildCard,[| $(buildArrow p e) >>> $a |])
buildD p (E.Generator _ p3 (E.LeftArrApp (return . toExp -> a) e )) = (p3,         [| $(buildArrow p e) >>> $a |])

buildArrow :: E.Pat -> E.Exp -> ExpQ
buildArrow E.PWildCard e= [| terminate $(return $ toExp e) |]
buildArrow p e | not $ any (flip elem $ freeVars p) (freeVars e)= [| terminate $(return $ toExp e) |]
               | otherwise = [| arr (\ $(return $ toPat p) ->
                   $(promote <$> intermediate p))
                   >>> arr (\ $(intermediate  p) -> $(promote <$> intermediate e))
               >>> arr (\ $(intermediate e) -> $(return $ toExp e)) |] -- >>= return . error .show
               where
                   intermediate vars = return $ tuplizer (TupP []) TupP <$> map (VarP . toName) $ freeVars vars

                                    {-
process ps (E.Proc _ b c) = Debug.Trace.trace (show b) $ process (ProcN 0 b (E.List []) [|Q.id|] : ps) c
process ps (E.Do statements) = (buildGr allNodes , fromAscList $ zip (view i <$> allNodes) allNodes)
    makeNodes ind (E.Generator _ p (E.LeftArrApp (returnQ . toExp -> e1) e2)) = (ind+1,StmtN ind p e2 e1)
    makeNodes ind (E.Qualifier (E.LeftArrApp (returnQ . toExp -> e1) e2)) = (ind+1,CmdN ind E.PWildCard e2 e1)
        ---}

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
  {- Closed, not needed
  | Apply -- (f,a) = f a   arr (\(f,a)->f a)
  | Curry
  | Uncurry
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
    right f = arr' [| mirror |] mirror >>> left f >>> arr' [| mirror |] mirror
    f +++ g = left f >>> right g
    f ||| g = f +++ g >>> arr' [| untag |] untag
mirror :: Either b a -> Either a b
mirror (Left x) = Right x
mirror (Right y) = Left y
untag :: Either t t -> t
untag (Left x) = x
untag (Right y) = y

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
        , ([| \a -> () |],Terminate [|()|])
        , ([| \a -> ((),()) |],Terminate [|()|] :*** Terminate [|()|])
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
fromAExp (Arr f) = appE [|arr|] f
fromAExp (First f) = appE [|first|] (fromAExp f)
fromAExp (Second f) = appE [|second|] (fromAExp f)
fromAExp (f :>>> g) = infixE (Just (fromAExp f)) [|(>>>)|] (Just (fromAExp g))
fromAExp (Loop f) = appE [|loop|] (fromAExp f)
fromAExp (LoopD i f) = appE (appE [|loopD|] i) f
fromAExp (ArrM i) = appE [|arrM|] i
fromAExp (Delay i) = appE [|delay|] i
fromAExp (Lft f) = appE [|left|] (fromAExp f)
fromAExp (Lift f) = f
fromAExp (f :*** g) = infixE (Just (fromAExp f)) [|(***)|] (Just (fromAExp g)) -- Not in original CCA. 2015-TB
fromAExp (f :&&& g) = infixE (Just (fromAExp f)) [|(&&&)|] (Just (fromAExp g)) -- Not in original CCA. 2015-TB

simplify :: String -> String
simplify = unwords . map (unwords . map aux . words) . lines
  where aux (c:x) | not (isAlpha c) = c : aux x
        aux x = let (_, v) = break (=='.') x
                in if length v > 1 then aux (tail v)
                                   else x


{-
findUnit :: IntMap NodeE -> [Int]
findUnit (toList -> l) = map fst $ Prelude.filter ( (== 0)  . length . freeVars . snd) l
newtype P = P NodeE
instance Eq NodeE where
    (==) = (==) `on` view i
instance Ord NodeE where
    compare = compare `on` view i

data Expression = Expression {getEV::Vertex,getPattern::E.Pat,getEE::ExpQ}
instance Eq Expression where
     (==) = (==) `on` getEV
instance Show Expression where
  show (Expression v p _) = "Expression: " ++ show v ++ show p


buildExp :: IntMap NodeE -> Graph -> [Vertex] -> [Expression] -> ExpQ
buildExp (toList -> [(0,ProcN (-1) E.PWildCard _ e)]) _ [0] [] = e
buildExp _ _ [] [Expression _ _ e] = e
buildExp _ _ [g] [Expression v _ e] | g==v = e
buildExp (fst . findMax -> target) _ _ exps | elem target (map getEV exps) = getEE . fromJust $ Data.List.find ( (==) target . getEV) exps -- got target early, effects?
buildExp intmap@(fst . findMax -> target) graph [] exps = buildExp intmap graph [target] exps
buildExp intmap graph goals exps = ifProgress
    where
        ifProgress = if (goals==newGoals) && (exps==newExps) then buildExp intmap graph (vertices graph)  exps  --error "loop detected in arrow TH"
                                                             else Debug.Trace.trace ("called " ++ show goals) $ buildExp intmap graph newGoals newExps
        flag ind = all (flip elem (map getEV exps)) $ (transposeG graph) ^. ix ind -- tells if a vertex is obtainable
        flags = findIndices flag goals -- lists obtainable goal indices
        flagsWithEmpty = [head flags]
        (newGoals,newExps) = Debug.Trace.trace ("flagged goals: " ++ show flags ++ "out of " ++ show goals ++ " and exps " ++ show exps)
                                $ step (goals,exps) (map ( (Data.List.!!) goals) flags)
        step (goals',exps') [] = (goals',exps')
        step (goals',exps') (flagged:rest) = Debug.Trace.trace (show (goals',exps')) step helper rest
            where
                newGoals2 = graph ^. ix flagged
                helper = (nub $ (Data.List.delete flagged goals') ++ newGoals2, newExps2 ++ remainingExps)
                helper2 = catMaybes $ map (flip elemIndex $ getEV <$> exps') $ (transposeG graph) ^. ix flagged --indeces in exps of needed exps
                reqExps = map ((Data.List.!!) exps') helper2
                remainingExps = (Data.List.\\) exps' reqExps
                newExps2 =replicate (max 1 $ length newGoals2) $
                                Expression flagged thisPat $ createConnection flagged reqExps thisExp currentArrow --createExp reqExps
                thisNode = Debug.Trace.trace (show flagged ++ show intmap) $ intmap ^?! ix flagged
                thisPat = Debug.Trace.trace (show "pats :" ++ show flagged) $ thisNode ^. pat
                thisExp = Debug.Trace.trace (show flagged ++ "exp :" ++ show (reqExps)++ show thisPat)
                         $ thisNode ^. expr
                currentArrow = Debug.Trace.trace (show "arr :" ++ show (flagged)) $
                            intmap ^?! ix flagged . arrowE

createConnection :: Int -> [Expression] -> E.Exp -> ArrowExp -> ExpQ
createConnection 0 [] _ arrowExp = [| $arrowExp |] -- should only be the original req. This doesn't visit literal signaled arrows. No SIDE EFFECTS?
--createConnection _ [] e arrowExp = [| arr (\a -> $(returnQ $ toExp e)) >>> $arrowExp |] -- should only be the original req. This doesn't visit literal signaled arrows. No SIDE EFFECTS?
createConnection _ exps thisExp arrowExp = defaultConnection exps thisExp arrowExp

-- tuplize may break for oddly shaped tuples
defaultConnection :: [Expression] -> E.Exp -> ArrowExp -> ExpQ
defaultConnection [] thisExp arrowExp =
    [| $(fixTuple E.PWildCard thisExp)
        >>> $arrowExp |]
        {-
defaultConnection pats@[e1,e2] thisExp arrowExp = case thisExp of
    E.Tuple E.Boxed [t1,t2]
         |  all (flip elem (toName <$> freeVars (getPattern e1))) (toName <$> freeVars t1)
             && (all (flip elem (toName <$> freeVars (getPattern e2))) (toName <$> freeVars t2))
                         -> error "hi" --[| $(getEE e1) *** $(getEE e2) >>> $(fixTuple (getPattern e1) t1) *** $(fixTuple (getPattern e2) t2) |]                        -- ***
         |  all (flip elem (toName <$> freeVars (getPattern e2))) (toName <$> freeVars t1)
             && (all (flip elem (toName <$> freeVars (getPattern e1))) (toName <$> freeVars t2))
                         -> [| coidr >>> ($(getEE e2) >>> $(fixTuple (getPattern e2) t1)) *** ($(getEE e1) >>> $(fixTuple (getPattern e1) t2)) >>> $arrowExp |]                        -- ***
    _ ->

            [| $(getEE e1) &&& $(getEE e2) >>> $(fixTuple (tuplize $ getPattern <$> pats) thisExp) >>> $arrowExp |]
        -}
defaultConnection exps thisExp arrowExp =
    [| $(foldl1 (&:&) (getEE <$> exps))
         >>> $(fixTuple (tuplize $ getPattern <$> exps) thisExp)
        >>> $arrowExp |]

(*:*) :: ExpQ -> ExpQ -> ExpQ
expr1 *:* expr2 = uInfixE expr1 (varE $ mkName "***") expr2
(&:&) :: ExpQ -> ExpQ -> ExpQ
expr1 &:& expr2 = uInfixE expr1 (varE $ mkName "&&&") expr2

process :: [NodeE] -> E.Exp -> (Graph,IntMap NodeE)
process ps (E.Proc _ b c) = Debug.Trace.trace (show b) $ process (ProcN 0 b (E.List []) [|Q.id|] : ps) c
process ps (E.Do statements) = (buildGr allNodes , fromAscList $ zip (view i <$> allNodes) allNodes)
    where
        allNodes = ps ++ (snd $ mapAccumL makeNodes 1 statements)
        makeNodes ind (E.Generator _ p (E.LeftArrApp (returnQ . toExp -> e1) e2)) = (ind+1,StmtN ind p e2 e1)
        makeNodes ind (E.Qualifier (E.LeftArrApp (returnQ . toExp -> e1) e2)) = (ind+1,CmdN ind E.PWildCard e2 e1)
        --makeNodes ind (E.LetStmt (E.BDecls (E.PatBind _ p _ (E.UnGuardedRhs rhs) binds :[]))) = (ind+1,StmtN ind p rhs [| Q.id |])
        makeNodes _ _ = error "process can only process Generators and Qualifier in Do statements"
process [] (returnQ . toExp -> e) = (buildG (0,0) [] , singleton 0 $ ProcN (-1) E.PWildCard (E.List []) e)
process _ e = error $ "does not process rec yet" ++ show e

buildGr :: [NodeE] -> Graph
buildGr n = buildG (0,length n -1) $ makeEdges n

makeEdges :: [NodeE] -> [Edge]
makeEdges [] = []
makeEdges (n:ns) = (makeEdges ns) ++ (catMaybes $ map (makeEdge (Set.fromList $ freeVars $ P n) (view i n)) ns)

makeEdge :: Set.Set E.Name -> Int -> NodeE -> Maybe Edge
makeEdge names ind node = if Set.null f then Nothing else Just (ind,view i node)
    where f = names `Set.intersection` (Set.fromList $ freeVars node)

instance FreeVars NodeE where
    freeVars (ProcN _ _ _ _) = []
    freeVars ex = freeVars $ ex ^?! expr --ProcN has no freeVars in non-existant expression
instance FreeVars P where
    freeVars (P ex) = freeVars $ ex ^. pat
---}
