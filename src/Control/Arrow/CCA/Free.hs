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
    arrow,into,buildA,
    cleanNames,parseMode,arrFixer,fixity,
    --AExp(..),ASyn(..),fromAExp,findM,eqM,fromASyn,printCCA,norm
    simplify,category,C.Dict(..),
    transformExp,toExp',FreeCCA(..),catplate,printExp
    ) where
import qualified Language.Haskell.Exts as E
import Control.Category
import Language.Haskell.Meta
import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Quote
import Language.Haskell.Meta.Utils
import Control.Arrow.CCA -- no Q or with Q?
import Control.Arrow hiding ((&&&),(***),first,second)
import qualified Control.Category as Q
import Data.List (filter,partition)
import Language.Haskell.TH.Utilities
import Data.Maybe
import Control.Lens hiding (Bifunctor)
import Control.Applicative
import Control.Arrow.TH.Structural

import Control.Category.Associative
import Control.Category.Structural
import Control.Category.Monoidal
import Control.Category.Cartesian
import Control.Categorical.Bifunctor
import           Prelude             hiding (id, (.),fst,snd)
import qualified Data.Generics       as G (everywhere,mkT)
import           Data.Char           (isAlpha)
import Data.Data
import qualified Data.Constraint as C
import Control.Monad.Trans.Maybe
import Control.Monad
import Control.Category.Free
import Control.Categorical.Bifunctor.Free
import Control.Category.Associative.Free
import Control.Category.Structural.Free
import Control.Category.Monoidal.Free
import Data.Generics.Multiplate
--import Control.Arrow.CCA.AExp(fixity,areExpAEq',simplify,printCCA)
import Data.Functor.Constant

parseMode :: E.ParseMode
parseMode = E.defaultParseMode{E.extensions=[E.EnableExtension E.Arrows],E.fixities=Just E.baseFixities}

arrow :: QuasiQuoter
arrow = QuasiQuoter {
  quoteExp = \input -> case E.parseExpWithMode parseMode input of
      E.ParseOk result -> buildA result
      E.ParseFailed l err -> error $ "arrow QuasiQuoter: " ++ show l ++ " " ++ show err
  , quotePat = error "cannot be patterns."
  , quoteDec = \input -> case E.parseDeclWithMode parseMode input of
      E.ParseOk _ -> error "arrow quasiQuoter for Dec not defined"
      E.ParseFailed l err -> error $ "arrow QuasiQuoter in Decl: " ++ show l ++ " " ++ show err
  , quoteType = error "cannot be types."
    }

transformExp :: Exp -> [Exp -> Q (Maybe Exp)] -> Q Exp
transformExp result rules = do
    let
        rules' expr = runMaybeT . msum $ ( MaybeT . fmap cleanNames . flip ($) expr) <$> rules
        res2 = cleanNames result
    rewriteM (rules' . transform fixity) res2

--category :: C.Dict (con a) -> [(con a => TExp (a b c) -> (Q (TExp (a b c))))] -> QuasiQuoter
category :: [[Exp -> Q (Maybe Exp)]] -> QuasiQuoter
category rules = QuasiQuoter {
  quoteExp = \input -> case E.parseExpWithMode parseMode input of
      E.ParseOk result -> do
          res <- buildA result
          res2 <- foldM transformExp res rules
          --reportWarning $ pprint res2
          return res2
      E.ParseFailed l err -> error $ "arrow QuasiQuoter: " ++ show l ++ " " ++ show err
  , quotePat = error "cannot be patterns."
  , quoteDec = error "category: cannot by dec"
  , quoteType = error "cannot be types."
    }

-- | Replaces expressions of `arr`, `arrM`, `delay`, and `returnA` with
-- the versions that have their arguments lifted to TH.
arrFixer :: Exp -> ExpQ
arrFixer = rewriteM arg
    where
        arg (AppE (VarE (Name (OccName "arr") _)) e) =
            Just <$> [| arr' (returnQ $(lift e)) $(returnQ e) |]
        arg (AppE (VarE (Name (OccName "arrM") _)) e) =
            Just <$> [| arrM' (returnQ $(lift e)) $(returnQ e) |]
        arg (AppE (VarE (Name (OccName "delay") _)) e) =
            Just <$> [| delay' (returnQ $(lift e)) $(returnQ e) |]
        arg (VarE (Name (OccName "returnA") _)) =
            Just <$> [| arr' (returnQ $([| Q.id |] >>= lift)) Q.id |]
        arg (AppE (ConE (Name (OccName "Lift") _)) e) =   -- Huh?
            Just <$> returnQ e
        arg (AppE (VarE (Name (OccName "terminate") _)) e) =
            fmap Just [| terminate' (returnQ $(lift e)) $(returnQ e) |]
        arg _ = return Nothing

fixity :: Data a => a -> a
fixity = G.everywhere (G.mkT expf)
    where expf (UInfixE l oper r) = InfixE (Just l) oper (Just r)
          expf (InfixE (Just (ParensE l)) oper (Just r)) = InfixE (Just l) oper (Just r)
          expf (InfixE (Just l) oper (Just (ParensE r))) = InfixE (Just l) oper (Just r)
          expf e = e

buildA :: E.Exp -> ExpQ
buildA (E.Proc _ pat expr) = buildB pat expr
buildA expr = return $ toExp expr

buildB :: E.Pat -> E.Exp -> ExpQ
buildB pat (E.Do exps) = snd $ head final
    where rest = buildC (init exps) [(pat,[|id|])]
          final = buildC [last exps] rest
buildB pat s@(E.LeftArrApp _ _) = [| $(snd $ buildD' (E.Qualifier s) [(pat,[|id|])] )|]
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
buildD' stmt@(E.RecStmt _) s = (origp,do
    a <- [| $fixedTuple >>> loop ($fixedSetup >>> $joinedArrows >>> $fixedTuple2) |]
    --reportWarning $ pprint a
    returnQ a
    )
    where
          fixedTuple = foldl1 (&:&) (snd <$> s)
          fixedSetup = buildArr (tuplizer E.PWildCard (E.PTuple E.Boxed) $ (fst <$> s) ++ collectedPats)
                                (tuplizer (E.Var $ E.Special E.UnitCon) (E.Tuple E.Boxed) collectedExps)
          fixedTuple2 = [| diag |]
          (arrows,collectedExps,collectedPats) = collectRecData stmt
          origp = tuplizer E.PWildCard (E.PTuple E.Boxed) collectedPats
          joinedArrows = foldl1 (*:*) (return . toExp <$> arrows)
buildD' stmt s = (origp,[| $fixedTuple >>> $(returnQ $ toExp arrow') |])
    where
          fixedTuple = fixTuple (snd <$> s) (tuplizer E.PWildCard (E.PTuple E.Boxed) ( fst <$> s)) expr
          (arrow',expr,origp) = case stmt of
                                 (E.Qualifier (E.LeftArrApp arrows f)) -> (arrows,f,E.PWildCard)
                                 (E.Generator _ p (E.LeftArrApp arrows f)) -> (arrows,f,p)
                                 (E.LetStmt (E.BDecls [E.PatBind _ p _ (E.UnGuardedRhs f) _])) -> (eId,f,p) --only 1 let stmt
                                 a -> error $ show a

collectRecData :: E.Stmt -> ([E.Exp],[E.Exp],[E.Pat])
collectRecData (E.Generator _ pat (E.LeftArrApp arrow' expr)) = ([arrow'],[expr],[pat])
collectRecData (E.Qualifier (E.LeftArrApp arrow' expr)) = ([arrow'],[expr],[E.PWildCard])
collectRecData (E.LetStmt (E.BDecls decls)) = unzip3 $ map (\(E.PatBind _ p _ (E.UnGuardedRhs rhs) _) -> (eId,rhs,p)) decls
collectRecData (E.RecStmt stmts) = (\(a,b,c) -> (concat a,concat b,concat c)) $ unzip3 $ map collectRecData stmts
collectRecData x = error $ "Error in collection of expressions: " ++ show x

eId :: E.Exp
eId = E.Var (E.UnQual $ E.Ident "id")

data ArrowOp (k:: * -> * -> *) a b where
    Arr :: (a -> b) -> ArrowOp k a b
    Arr' :: ExpQ -> k a b -> ArrowOp k a b
data CCAOp m i (p:: * -> * -> *) (k:: * -> * -> *) a b where
    Delay :: ExpQ -> CCAOp m i p k a a
    Delay' :: ExpQ -> a -> CCAOp m i p k a a
    LoopD :: ExpQ -> ExpQ -> CCAOp m i p k a b
    ArrM  :: ExpQ -> CCAOp m i p k a b
    ArrM'  :: ExpQ -> (a -> m b) -> CCAOp m i p k a b
data TerminateOp (k :: * -> * -> *) a i where
    Terminate :: i -> TerminateOp k a i
    Terminate' :: ExpQ -> i -> TerminateOp k a i

-- | Operations from the base @k@, plus free all the structural operations.
data FreeCCA m i p k a b where
    FreeCCABaseOp :: k a b -> FreeCCA m i p k a b
    FreeCCATerminateOp :: TerminateOp (FreeCCA m i p k) a b
                       -> FreeCCA m i p k a b
    FreeCCACategoryOp :: CategoryOp (FreeCCA m i p k) a b
                      -> FreeCCA m i p k a b
    FreeCCAPfunctorOp :: PFunctorOp p (FreeCCA m i p k) a b
                      -> FreeCCA m i p k a b
    FreeCCAQfunctorOp :: QFunctorOp p (FreeCCA m i p k) a b
                      -> FreeCCA m i p k a b
    FreeCCABifunctorOp :: BifunctorOp p (FreeCCA m i p k) a b
                       -> FreeCCA m i p k a b
    FreeCCAWeakenOp :: WeakenOp p a b -> FreeCCA m i p k a b
    FreeCCAContractOp :: ContractOp p a b -> FreeCCA m i p k a b
    FreeCCASymmetricOp :: SymmetricOp p a b -> FreeCCA m i p k a b
    FreeCCALeftIdentityOp :: LeftIdentityOp i p a b
                          -> FreeCCA m i p k a b
    FreeCCARightIdentityOp :: RightIdentityOp i p a b
                           -> FreeCCA m i p k a b
    FreeCCAAssociativeOp :: AssociativeOp p a b
                         -> FreeCCA m i p k a b
    FreeCCAArrowOp :: ArrowOp k a b
                    -> FreeCCA m i p k a b
    FreeCCAOp :: CCAOp m i p k a b
               -> FreeCCA m i p k a b

data CCAPlate f = CCAPlate {catplate :: forall m i p k a b. FreeCCA m i p k a b -> f (FreeCCA m i p k a b)}
instance Multiplate CCAPlate where
    multiplate (CCAPlate f) = CCAPlate $ \case
        FreeCCABaseOp a -> pure (FreeCCABaseOp a)
        FreeCCATerminateOp a -> pure (FreeCCATerminateOp a)
        FreeCCACategoryOp Id -> pure (FreeCCACategoryOp Id)
        FreeCCACategoryOp (a :>>> b) -> (\x y -> FreeCCACategoryOp (x :>>> y)) <$> f a <*> f b
        FreeCCAPfunctorOp (First a) -> FreeCCAPfunctorOp . First <$> f a
        FreeCCAQfunctorOp (Second a) -> FreeCCAQfunctorOp . Second <$> f a
        FreeCCABifunctorOp (a :*** b) -> (\x y -> FreeCCABifunctorOp (x :*** y)) <$> f a <*> f b
        FreeCCAWeakenOp Fst -> pure (FreeCCAWeakenOp Fst)
        FreeCCAWeakenOp Snd -> pure (FreeCCAWeakenOp Snd)
        FreeCCAContractOp Diag -> pure (FreeCCAContractOp Diag)
        FreeCCASymmetricOp Swap -> pure (FreeCCASymmetricOp Swap)
        a@(FreeCCALeftIdentityOp _) -> pure a
        a@(FreeCCARightIdentityOp _) -> pure a
        a@(FreeCCAAssociativeOp _) -> pure a
        a@(FreeCCAArrowOp _) -> pure a
        a@(FreeCCAOp _) -> pure a
    mkPlate build = CCAPlate $ build catplate

printExp :: FreeCCA Identity () (,) (->) a b -> IO ()
printExp x = runQ (foldFor catplate toExp' x) >>= putStrLn . simplify . pprint

toExp' :: CCAPlate (Constant ExpQ)
toExp' = CCAPlate $ \case
    --FreeCCABaseOp a -> Constant [|a|]
    FreeCCACategoryOp Id -> Constant [|id|]
    FreeCCACategoryOp (a :>>> b) -> Constant [| $a' >>> $b' |]
        where
            a' = foldFor catplate toExp' a
            b' = foldFor catplate toExp' b
    FreeCCAWeakenOp Fst -> Constant [| fst |]
    FreeCCAWeakenOp Snd -> Constant [| snd |]
    FreeCCAPfunctorOp (First a) -> Constant $ [| first $a' |]
        where a' = foldFor catplate toExp' a
    FreeCCAQfunctorOp (Second a) -> Constant $ [| second $a' |]
        where a' = foldFor catplate toExp' a
    FreeCCABifunctorOp (a :*** b ) -> Constant $ [| $a' *** $b' |]
        where
            a' = foldFor catplate toExp' a
            b' = foldFor catplate toExp' b
    FreeCCAContractOp Diag -> Constant [| diag |]
    FreeCCASymmetricOp Swap -> Constant [| swap |]
    FreeCCALeftIdentityOp Idl -> Constant [| idl |]
    FreeCCALeftIdentityOp Coidl -> Constant [| coidl |]
    FreeCCARightIdentityOp Idr -> Constant [| idr |]
    FreeCCARightIdentityOp Coidr -> Constant [| coidr |]
    FreeCCAAssociativeOp Associate -> Constant [| associate |]
    FreeCCAAssociativeOp Coassociate -> Constant [| coassociate |]
    FreeCCAArrowOp (Arr' a _) -> Constant [| arr $a |]
    FreeCCAOp (ArrM' a _) -> Constant [| arrM $a |]
    FreeCCAOp (Delay' a _) -> Constant [| delay $a |]
    FreeCCATerminateOp (Terminate' a _) -> Constant [| terminate $a |]
    _ -> error "unable to convert to ExpQ"

instance Show (FreeCCA m i p k a b) where
    show (FreeCCABaseOp _) = "SomeArrow"
    show (FreeCCATerminateOp (Terminate _)) = "Terminate"
    show (FreeCCACategoryOp Id) = "Id"
    show (FreeCCACategoryOp (a :>>> b)) = show a ++ " >>> " ++ show b
    show (FreeCCAPfunctorOp (First a)) = "first (" ++ show a ++ ")"
    show (FreeCCAQfunctorOp (Second a)) = "second (" ++ show a ++ ")"
    show (FreeCCABifunctorOp (a :*** b)) = "(" ++ show a ++ " *** " ++ show b ++ ")"
    show (FreeCCAWeakenOp Fst) = "fst"
    show (FreeCCAWeakenOp Snd) = "snd"
    show (FreeCCAContractOp Diag) = "diag"
    show (FreeCCASymmetricOp Swap) = "swap"
    show (FreeCCALeftIdentityOp Idl) = "idl"
    show (FreeCCALeftIdentityOp Coidl) = "coidl"
    show (FreeCCARightIdentityOp Idr) = "idr"
    show (FreeCCARightIdentityOp Coidr) = "coidr"
    show (FreeCCAAssociativeOp Associate) = "associate"
    show (FreeCCAAssociativeOp Coassociate) = "coassociate"
    show (FreeCCAArrowOp (Arr' a _)) = "arrExpression " ++ show a
    show (FreeCCAOp (ArrM' a _)) = "arrExpression " ++ show a
    show (FreeCCATerminateOp (Terminate' a _)) = "arrExpression " ++ show a
    show _ = "someFreeCCAExpression"

simplify :: String -> String
simplify = unwords . map (unwords . map aux . words) . lines
  where aux (c:x) | not (isAlpha c) = c : aux x
        aux x = let (_, v) = break (=='.') x
                in if length v > 1 then aux (tail v)
                                   else x

instance Trans2 (FreeCCA m i p) where
    lift2 = FreeCCABaseOp

instance Category (FreeCCA m i p k) where
    id = FreeCCACategoryOp Id
    f . g = FreeCCACategoryOp (g :>>> f)

instance PFunctor p (FreeCCA m i p k)
instance QFunctor p (FreeCCA m i p k)
instance Bifunctor p (FreeCCA m i p k) where
    f *** g = FreeCCABifunctorOp (f :*** g)

instance Weaken p (FreeCCA m i p k) where
    fst = FreeCCAWeakenOp Fst
    snd = FreeCCAWeakenOp Snd

instance Contract p (FreeCCA m i p k) where
    diag = FreeCCAContractOp Diag

instance Associative p (FreeCCA m i p k) where
    associate = FreeCCAAssociativeOp Associate
    coassociate = FreeCCAAssociativeOp Coassociate
instance Symmetric p (FreeCCA m i p k) where
    swap = FreeCCASymmetricOp Swap
instance Exchange p (FreeCCA m i p k)

instance HasLeftIdentity i p (FreeCCA m i p k) where
    idl   = FreeCCALeftIdentityOp Idl
    coidl = FreeCCALeftIdentityOp Coidl
instance HasRightIdentity i p (FreeCCA m i p k) where
    idr   = FreeCCARightIdentityOp Idr
    coidr = FreeCCARightIdentityOp Coidr
instance HasIdentity i p (FreeCCA m i p k)

instance Monoidal i p (FreeCCA m i p k)
instance Cartesian i p (FreeCCA m i p k)
