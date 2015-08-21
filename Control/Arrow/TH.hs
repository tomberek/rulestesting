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
import Language.Haskell.Meta
import Language.Haskell.TH
import Language.Haskell.TH.Syntax

import Language.Haskell.TH.Quote
import Data.Generics.Uniplate.DataOnly
import Control.Arrow.Init
import Control.Arrow
import qualified Control.Category as Q
import Data.List (mapAccumL,findIndices,elemIndex,(\\),(!!),delete,nub,find)
import Data.Graph
import Data.Tree
import Data.IntMap hiding (map)
import qualified Data.Array as A
import Data.Function
import Language.Haskell.TH.Utilities
import qualified Data.Set as Set
import Data.Maybe
import Debug.Trace

-- | A 'QuasiQuoter' that desugars proc-do notation and prepares for
-- CCA optimization via `arr'` and `init'` usage.
arrow :: QuasiQuoter
arrow = QuasiQuoter {
    quoteExp = \input -> case parseArrow input of
        E.ParseOk result -> Debug.Trace.trace (unlines $
                [show $ topSort graph
                ,show graph
                ,show $ dfs graph (topSort graph)
                ,drawForest $ (fmap (fmap show) $ dfs graph (topSort graph))
                ,drawForest $ (fmap (fmap show) $ dfs (transposeG graph) (topSort $ transposeG graph))
                ])
                -- (go graphDFS nodes)
                go' nodes graph [0] [] >>= arrFixer
                where (graph,nodes) = process [] result
                      graphDFS = dfs graph (topSort graph)
        E.ParseFailed l err -> error $ show l ++ show err
      , quotePat = error "cannot be patterns."
      , quoteDec = error "cannot be declarations."
      , quoteType = error "cannot be types."
        }

type ArrowExp = E.Exp
data NodeE where
    ProcN :: Int -> E.Pat -> NodeE
    StmtN :: Int -> E.Pat -> E.Exp -> ArrowExp -> NodeE
    CmdN  :: Int -> E.Exp -> ArrowExp -> NodeE
newtype P = P NodeE
instance Eq NodeE where
    (==) = (==) `on` getId
instance Ord NodeE where
    compare = compare `on` getId

data Goal = Goal {getGV::Vertex,getGE::ExpQ}
data Expression = Expression {getEV::Vertex,getName::E.Name,getPattern::E.Pat,getEE::ExpQ}
instance Eq Expression where
     (==) = (==) `on` getEV
instance Show Expression where
  show (Expression v n _ _) = "Expression: " ++ show v ++ " named: " ++ show n

go' :: IntMap NodeE -> Graph -> [Vertex] -> [Expression] -> ExpQ
go' _ _ [] [Expression _ _ _ expr] = expr
go' _ _ [g] [Expression v _ _ expr] | g==v = expr
go' (fst . findMax -> target) _ _ exps | elem target (map getEV exps) = getEE . fromJust $ Data.List.find ( (==) target . getEV) exps
go' _ _ [] _ = error "multiple expressions, no goals"
go' mapping graph goals exps = go' mapping graph newGoals newExps
    where
        flag a = all (flip elem (map getEV exps)) $ (transposeG graph) `access` a -- tells if a vertex is obtainable
        flags = findIndices flag goals -- lists obtainable goal indeces
        (newGoals,newExps) = Debug.Trace.trace ("flagged goals: " ++ show flags ++ "out of " ++ show goals ++ " and exps " ++ show exps) 
                                $ step (goals,exps) (map ( (Data.List.!!) goals) flags)
        step (goals',exps') [] = (goals',exps')
        step (goals',exps') (flagged:rest) = Debug.Trace.trace (show (goals',exps')) step helper rest
            where
                expVs = map getEV exps'
                newGoals2 = graph `access` flagged
                helper = (nub $ (Data.List.delete flagged goals'), newExps2 ++ remainingExps)
                helper2 = catMaybes $ map (flip elemIndex expVs) $ (transposeG graph) `access` flagged --indeces in exps of needed exps
                reqExps = map ((Data.List.!!) exps') helper2
                remainingExps = (Data.List.\\) exps' reqExps
                newExps2 =replicate (max 1 $ length newGoals) $ createExp reqExps
                createExp [] = Debug.Trace.trace ("no reqs for " ++ show flagged) $ Expression flagged thisName thisPat [| $(currentArrow mapping flagged) |]
                createExp [Expression v _ p expr] = Debug.Trace.trace ("one req for " ++ show flagged ++ " is " ++ show v) $
                                  Expression flagged thisName thisPat [| $(patCorrection p thisExp expr) >>> $(currentArrow mapping flagged) |]
                -- ensure in the right order!
                createExp more = Debug.Trace.trace ("many req for " ++ show flagged ++ " is " ++ show more ++ " new order:" ++ show order) $
                                  Expression flagged thisName thisPat [| $(foldl1 (&:&) createTuple) >>> $(currentArrow mapping flagged) |]
                -- assumes that the vars are in a tuple, in order
                createTuple = catMaybes $ map (flip Prelude.lookup $ zip (map getName reqExps) (map getEE reqExps)) order
                thisNode = mapping ! flagged
                thisPat = getPat thisNode
                thisExp = getExp thisNode
                thisName = case freeVars thisPat of
                    (a:_) -> a
                    _ -> E.Ident "inCommand"
                order = freeVars $ getExp thisNode

(&:&) :: ExpQ -> ExpQ -> ExpQ
expr1 &:& expr2 = uInfixE expr1 (varE $ mkName "&&&") expr2

-- | Creates a lambda if needed from pattern to expression
patCorrection :: E.Pat -> E.Exp -> ExpQ -> ExpQ
patCorrection p@(E.PVar n) e@(E.Var qn) exp | toName qn == toName n = exp
                        | otherwise = [| $exp >>> arr (\ $(returnQ $ toPat p) -> $(returnQ $ toExp e)) |]
patCorrection p e@(E.App _ _) exp = [| $exp >>> arr (\ $(returnQ $ toPat p) -> $(returnQ $ toExp e)) |]
patCorrection p e exp = [| $exp >>> arr (\ $(returnQ $ toPat p) -> $(returnQ $ toExp e)) |]

go :: Forest Vertex -> IntMap NodeE -> ExpQ
go [] mapping = [| Q.id|]
go [Node a []] mapping = [| $(currentArrow mapping a) |]
go [Node a rest] mapping = [| $(go rest mapping) >>> $(currentArrow mapping a) |]
go [Node a rest,Node b rest2] mapping =
    [|  $(go rest mapping) >>> $(currentArrow mapping a)  &&&  $(go rest2 mapping) >>> $(currentArrow mapping b)  |]
go forest mapping = error $ unlines ["only defined for 2-branching",drawForest $ fmap (fmap show) forest]
access b c = b A.! c

process :: [NodeE] -> E.Exp -> (Graph,IntMap NodeE)
process ps (E.Proc a b c) = process (ProcN 0 b:ps) c
process ps (E.Do statements) = (buildGr $ allNodes,fromAscList $ zip (map getId allNodes) allNodes)
    where
        allNodes = ps ++ (snd $ mapAccumL makeNodes 1 statements)
        makeNodes i (E.Generator _ p (E.LeftArrApp e1 e2)) = (i+1,StmtN i p e2 e1)
        makeNodes i (E.Qualifier (E.LeftArrApp e1 e2)) = (i+1,CmdN i e2 e1)

groupNodes :: [Int] -> [NodeE] -> [[NodeE]]
groupNodes (n:ns) nodes = undefined

getId (ProcN i _)=i
getId (StmtN i _ _ _)=i
getId (CmdN i _ _) = i
currentArrow mapping a= getArrow $ mapping ! a
getArrow (StmtN _ p e a) = returnQ $ toExp a
getArrow (CmdN _ e a) = [|  $(returnQ $ toExp a) |]
getArrow _ = [| Q.id |]
getExp (ProcN _ _) = error "no expression in ProcN"
getExp (StmtN i _ e _) = e
getExp (CmdN i e _) = e
getPat (ProcN _ p) = p
getPat (StmtN _ p _ _) = p
getPat (CmdN i e _) = E.PWildCard --error $ "no pattern in CmdN:" ++ show e ++ " at line:" ++ show i

buildGr :: [NodeE] -> Graph
buildGr n = buildG (0,length n -1) $ makeEdges n
makeEdges :: [NodeE] -> [Edge]
makeEdges [] = []
makeEdges (n:ns) = (makeEdges ns) ++ (catMaybes $ map (makeEdge (Set.fromList $ freeVars $ P n) (getId n)) ns)

makeEdge :: Set.Set E.Name -> Int -> NodeE -> Maybe Edge
makeEdge names i node = if Set.null f then Nothing else Just (i,getId node)
    where
          f = names `Set.intersection` (Set.fromList $ freeVars node)

instance FreeVars NodeE where
    freeVars (StmtN _ _ e _) = freeVars e
    freeVars (CmdN _ e _) = freeVars e
instance FreeVars P where
    freeVars (P (ProcN _ p)) = freeVars p
    freeVars (P (StmtN _ p _ _)) = freeVars p
    freeVars (P (CmdN _ p _)) = []

arrowParseMode :: E.ParseMode
arrowParseMode = E.defaultParseMode{E.extensions=[E.EnableExtension E.Arrows]}
parseArrow :: String -> E.ParseResult E.Exp
parseArrow = E.parseExpWithMode arrowParseMode

-- | Replaces expressions of `arr`, `arrM`, `init`, and `returnA` with
-- the versions that have their arguments lifted to TH.
arrFixer :: Exp -> ExpQ
arrFixer = rewriteM arg
    where
        arg (AppE (VarE (Name (OccName "arr") _)) expr) =
            fmap Just [| arr' (returnQ $(lift expr)) $(returnQ expr) |]
        arg (AppE (VarE (Name (OccName "arrM") _)) expr) =
            fmap Just [| arrM' (returnQ $(lift expr)) $(returnQ expr) |]
        arg (AppE (VarE (Name (OccName "init") _)) expr) =
            fmap Just [| init' (returnQ $(lift expr)) $(returnQ expr) |]
        arg (VarE (Name (OccName "returnA") _)) =
            fmap Just [| arr' (returnQ $([| id |] >>= lift)) id |]
        arg _ = return Nothing

---}
---}
