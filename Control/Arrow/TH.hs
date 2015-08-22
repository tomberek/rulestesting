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
import Control.Arrow.Init
import Control.Arrow
import qualified Control.Category as Q
import Data.List (mapAccumL,findIndices,elemIndex,(\\),(!!),delete,nub,find)
import Data.Graph
import Data.Tree
import Data.IntMap hiding (map)
import Data.Function
import Language.Haskell.TH.Utilities
import qualified Data.Set as Set
import Data.Maybe
import Debug.Trace
import Control.Lens
import Control.Applicative
import Data.Generics.Schemes
import Data.Generics.Aliases (mkT)
import Data.Data

type ArrowExp = ExpQ
data NodeE =
    ProcN {_i::Int,_pat::E.Pat,_arrowE::ArrowExp}
    | StmtN {_i::Int,_pat::E.Pat,_expr::E.Exp,_arrowE::ArrowExp}
    | CmdN  {_i::Int,_pat::E.Pat,_expr::E.Exp,_arrowE::ArrowExp}
    | LetN {_i::Int,_pat::E.Pat,_expr::E.Exp,_arrowE::ArrowExp}
makeLenses ''NodeE

-- | A 'QuasiQuoter' that desugars proc-do notation and prepares for
-- CCA optimization via `arr'` and `init'` usage.
arrow :: QuasiQuoter
arrow = QuasiQuoter {
    quoteExp = \input -> case E.parseExpWithMode E.defaultParseMode{E.extensions=[E.EnableExtension E.Arrows],E.fixities=Just (E.baseFixities)} input of
        E.ParseOk result -> Debug.Trace.trace (unlines $
                [show $ topSort graph
                ,show graph
                ,show $ dfs graph (topSort graph)
                ,drawForest $ (fmap (fmap show) $ dfs graph (topSort graph))
                ,drawForest $ (fmap (fmap show) $ dfs (transposeG graph) (topSort $ transposeG graph))
                ])
                buildExp nodes graph [0] [] >>= arrFixer
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

data Expression = Expression {getEV::Vertex,getName::E.Name,getPattern::E.Pat,getEE::ExpQ}
instance Eq Expression where
     (==) = (==) `on` getEV
instance Show Expression where
  show (Expression v n _ _) = "Expression: " ++ show v ++ " named: " ++ show n

buildExp :: IntMap NodeE -> Graph -> [Vertex] -> [Expression] -> ExpQ
buildExp _ _ [] [Expression _ _ _ e] = e
buildExp _ _ [g] [Expression v _ _ e] | g==v = e
buildExp (fst . findMax -> target) _ _ exps | elem target (map getEV exps) = getEE . fromJust $ Data.List.find ( (==) target . getEV) exps -- got target early, effects?
buildExp _ _ [] _ = error "multiple expressions, no goals"
buildExp intmap graph goals exps = buildExp intmap graph newGoals newExps
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
                                Expression flagged thisName thisPat $ createConnection reqExps thisExp currentArrow --createExp reqExps
                createExp [] = Debug.Trace.trace ("no reqs for " ++ show flagged) $ Expression flagged thisName thisPat [| $currentArrow |]
                createExp [Expression v _ p e] = Debug.Trace.trace ("one req for " ++ show flagged ++ " is " ++ show v) $
                                  Expression flagged thisName thisPat [| $(patCorrection e p thisExp) >>> $currentArrow |]
                -- fix the multi-case with patCorrection
                createExp more = Expression flagged thisName thisPat [| $(foldl1 (&:&) createTuple) >>> $currentArrow |]
                -- assumes that the vars are in a tuple, in order
                createTuple = map getEE $ catMaybes $ map (flip Prelude.lookup $ zip (map getName reqExps) reqExps) $ freeVars thisExp
                    where order = freeVars thisExp
                thisNode = intmap ! flagged
                thisPat = thisNode ^. pat
                thisExp = thisNode ^?! expr
                currentArrow = intmap ^?! ix flagged . arrowE
                thisName = case freeVars thisPat of
                    (x:_) -> x
                    _ -> E.Ident "ShouldBeFinalGoal"

createConnection :: [Expression] -> E.Exp -> ArrowExp -> ExpQ
createConnection []   thisExp arrowExp = [| $arrowExp |] -- should only be the original req. This doesn't visit literal signaled arrows. No SIDE EFFECTS?
--createConnection []   thisExp arrowExp = [| arr (const $(returnQ $ toExp thisExp)) >>> $arrowExp |] -- for example: a literal needs no other expression for input
--createConnection ex@[Expression _ _ pat@(E.PVar n) expr] thisExp@(E.Var qn) arrowExp | toName qn == toName n = [| $expr >>> $arrowExp |]
createConnection exps thisExp arrowExp = defaultConnection exps thisExp arrowExp

--defaultConnection exps thisExp arrowExp = [| $(foldl1 (&:&) inExps) >>> arr (\ $(returnQ . toPat $ tuplize inPats) -> $(returnQ $ toExp thisExp)) >>> $arrowExp |]
defaultConnection :: [Expression] -> E.Exp -> ArrowExp -> ExpQ
defaultConnection exps thisExp arrowExp = [| $(foldl1 (&:&) (getEE <$> exps))
                                          >>> arr (\ $(returnQ . toPat $ tuplize $ getPattern <$> exps) -> $(returnQ $ toExp thisExp))
                                          >>> $arrowExp |]
                                          {-
defaultConnection exps thisExp arrowExp = let
        inExps = getEE <$> exps'
        inPats = getPattern <$> exps'
        exps' = catMaybes $ map (flip Prelude.lookup $ zip (map getName exps) exps) $ freeVars thisExp --reorder for easy tupling
        removedIds e=
            ifM (isId $ fixity <$> [| (\ $(returnQ . toPat $ tuplize $ getPattern <$> e) -> $(returnQ $ toExp thisExp))  |] )
                                   arrowExp
                                   [| arr (\ $(returnQ . toPat $ tuplize $ getPattern <$> e) -> $(returnQ $ toExp thisExp)) >>> $arrowExp |]
        in [| $(foldl1 (&:&) inExps) >>> $(removedIds exps') |]
                                          -}

fixity :: Data a => a -> a
fixity = everywhere' (mkT expf)
    where expf (UInfixE l o r) = InfixE (Just l) o (Just r)
          expf e = e
-- | Creates an arr lambda if needed from pattern to expression
patCorrection :: ExpQ -> E.Pat -> E.Exp -> ExpQ
patCorrection e2 (E.PVar n) e@(E.Var qn) | toName qn == toName n = e2
                         | otherwise = [| $e2 >>> arr (\ $(returnQ $ toPat $ E.PVar n) -> $(returnQ $ toExp e)) |]
patCorrection e2 p e@(E.App _ _) = const id p [| $e2 >>> arr (\ $(returnQ $ toPat p) -> $(returnQ $ toExp e)) |] --const trick to "use" p argument
patCorrection e2 p e = const id p [| $e2 >>> arr (\ $(returnQ $ toPat p) -> $(returnQ $ toExp e)) |]

(&:&) :: ExpQ -> ExpQ -> ExpQ
expr1 &:& expr2 = uInfixE expr1 (varE $ mkName "&&&") expr2

process :: [NodeE] -> E.Exp -> (Graph,IntMap NodeE)
process ps (E.Proc _ b c) = process (ProcN 0 b [|Q.id|] : ps) c
process ps (E.Do statements) = (buildGr $ allNodes,fromAscList $ zip (view i <$> allNodes) allNodes)
    where
        allNodes = ps ++ (snd $ mapAccumL makeNodes 1 statements)
        makeNodes ind (E.Generator _ p (E.LeftArrApp (returnQ . toExp -> e1) e2)) = (ind+1,StmtN ind p e2 e1)
        makeNodes ind (E.Qualifier (E.LeftArrApp (returnQ . toExp -> e1) e2)) = (ind+1,CmdN ind E.PWildCard e2 e1)
        makeNodes ind (E.LetStmt (E.BDecls (E.PatBind _ p _ (E.UnGuardedRhs rhs) binds :[]))) = (ind+1,StmtN ind p rhs [| Q.id |])
        makeNodes _ _ = error "process can only process Generators and Qualifier in Do statements, only one let stms"
process _ _ = error "does not process rec yet"

buildGr :: [NodeE] -> Graph
buildGr n = buildG (0,length n -1) $ makeEdges n

makeEdges :: [NodeE] -> [Edge]
makeEdges [] = []
makeEdges (n:ns) = (makeEdges ns) ++ (catMaybes $ map (makeEdge (Set.fromList $ freeVars $ P n) (view i n)) ns)

makeEdge :: Set.Set E.Name -> Int -> NodeE -> Maybe Edge
makeEdge names ind node = if Set.null f then Nothing else Just (ind,view i node)
    where f = names `Set.intersection` (Set.fromList $ freeVars node)

instance FreeVars NodeE where
    freeVars (ProcN _ _ _) = []
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
            fmap Just [| arr' (returnQ $([| id |] >>= lift)) id |]
        arg _ = return Nothing