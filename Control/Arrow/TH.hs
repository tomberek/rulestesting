{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ViewPatterns #-}
{- |
Module      :  Control.Arrow.TH
Description :  Arrow notation QuasiQuoter
Copyright   :  (c) 2015 Thomas Bereknyei
License     :  BSD3
Maintainer  :  Thomas Bereknyei <tomberek@gmail.com>
Stability   :  unstable
Portability :  TemplateHaskell,QuasiQuotes,ViewPatterns

-}
module Control.Arrow.TH (arrow,arrFixer) where
import qualified Language.Haskell.Exts as E
import Prelude hiding ((.))
import Control.Category
import Language.Haskell.Meta
import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Quote
import Control.Arrow.Init
import Control.Arrow
import qualified Control.Category as Q
import Data.List (mapAccumL,findIndices,elemIndex,(\\),(!!),delete,nub,find)
import Data.Graph

import Data.IntMap hiding (map)
import Data.Function(on)
import Language.Haskell.TH.Utilities
import qualified Data.Set as Set
import Data.Maybe
import Debug.Trace
import Control.Lens
import Control.Applicative

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

-- | A 'QuasiQuoter' that desugars proc-do notation and prepares for
-- CCA optimization via `arr'` and `init'` usage.
arrow :: QuasiQuoter
arrow = QuasiQuoter {
    quoteExp = \input -> case E.parseExpWithMode E.defaultParseMode{E.extensions=[E.EnableExtension E.Arrows],E.fixities=Just (E.baseFixities)} input of
        E.ParseOk result -> buildExp nodes graph [0] [] >>= arrFixer
                where (graph,nodes) = process [] result
        E.ParseFailed l err -> error $ show l ++ show err
      , quotePat = error "cannot be patterns."
      , quoteDec = error "cannot be declarations."
      , quoteType = error "cannot be types."
        }

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
buildExp intmap graph goals exps = Debug.Trace.trace ("called " ++ show goals) $ buildExp intmap graph newGoals newExps
    where
        flag ind = all (flip elem (map getEV exps)) $ (transposeG graph) ^. ix ind -- tells if a vertex is obtainable
        flags = findIndices flag goals -- lists obtainable goal indeces
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
createConnection _ [] e arrowExp = [| arr (\a -> $(returnQ $ toExp e)) >>> $arrowExp |] -- should only be the original req. This doesn't visit literal signaled arrows. No SIDE EFFECTS?
createConnection _ exps thisExp arrowExp = defaultConnection exps thisExp arrowExp

defaultConnection :: [Expression] -> E.Exp -> ArrowExp -> ExpQ
defaultConnection exps thisExp arrowExp = [| $(foldl1 (&:&) (getEE <$> exps))
                                          >>> arr (\ $(returnQ . toPat $ tuplize $ getPattern <$> exps) -> $(returnQ $ toExp thisExp))
                                          >>> $arrowExp |]

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

-- | Replaces expressions of `arr`, `arrM`, `init`, and `returnA` with
-- the versions that have their arguments lifted to TH.
arrFixer :: Exp -> ExpQ
arrFixer = rewriteM arg
    where
        arg (AppE (VarE (Name (OccName "arr") _)) e) =
            fmap Just [| arr' (returnQ $(lift e)) $(returnQ e) |]
        arg (AppE (VarE (Name (OccName "arrM") _)) e) =
            fmap Just [| arrM' (returnQ $(lift e)) $(returnQ e) |]
        arg (AppE (VarE (Name (OccName "init") _)) e) =
            fmap Just [| init' (returnQ $(lift e)) $(returnQ e) |]
        arg (VarE (Name (OccName "returnA") _)) =
            fmap Just [| arr' (returnQ $([| Q.id |] >>= lift)) Q.id |]
        arg _ = return Nothing