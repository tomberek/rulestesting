{-# LANGUAGE RankNTypes #-}
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
module Control.Arrow.TH (arrow,arrowInit,arrowG,arrFixer) where
import qualified Language.Haskell.Exts as E
import Language.Haskell.Meta
import Language.Haskell.TH
import Language.Haskell.TH.Syntax

import Language.Haskell.TH.Quote
import Data.Generics.Uniplate.DataOnly
import Control.Arrow.Init
import Control.Arrow
import Data.List (mapAccumL)
import Data.Graph
import Data.Function
import Language.Haskell.TH.Utilities
import qualified Data.Set as Set
import Data.Maybe

type ArrowExp = E.Exp
-- | A 'QuasiQuoter' that desugars proc-do notation.
arrowG :: QuasiQuoter
arrowG = arrowInit{
    quoteExp = \input -> case parseArrow input of
        E.ParseOk result -> error $ show $ topSort $ process [] result
        E.ParseFailed l err -> error $ show l ++ show err}

data Node where
    ProcN :: Int -> E.Pat -> Node
    StmtN :: Int -> E.Pat -> E.Exp -> ArrowExp -> Node
    CmdN  :: Int -> E.Exp -> ArrowExp -> Node
newtype P = P Node
instance Eq Node where
    (==) = (==) `on` getId
instance Ord Node where
    compare = compare `on` getId

process ps (E.Proc a b c) = process (ProcN 0 b:ps) c
process ps (E.Do statements) = buildGr $ ps ++ (snd $ mapAccumL makeNodes 1 statements)
    where
        makeNodes i (E.Generator _ p (E.LeftArrApp e1 e2)) = (i+1,StmtN i p e2 e1)
        makeNodes i (E.Qualifier (E.LeftArrApp e1 e2)) = (i+1,CmdN i e2 e1)

groupNodes :: [Int] -> [Node] -> [[Node]]
groupNodes (n:ns) nodes = undefined

getId (ProcN i _)=i
getId (StmtN i _ _ _)=i
getId (CmdN i _ _) = i

buildGr :: [Node] -> Graph
buildGr n = buildG (0,length n - 1) $ makeEdges n
makeEdges :: [Node] -> [Edge]
makeEdges [] = []
makeEdges (n:ns) = (makeEdges ns) ++ (catMaybes $ map (makeEdge (freeVars $ P n) (getId n)) ns)

makeEdge :: Set.Set E.Name -> Int -> Node -> Maybe Edge
makeEdge names i node = if Set.null f then Nothing else Just (i,getId node)
    where
          f = names `Set.intersection` (freeVars node)

instance FreeVars Node where
    freeVars (StmtN _ _ e _) = freeVars e
    freeVars (CmdN _ e _) = freeVars e
instance FreeVars P where
    freeVars (P (ProcN _ p)) = freeVars p
    freeVars (P (StmtN _ p _ _)) = freeVars p
    freeVars (P (CmdN _ p _)) = Set.empty

-- proc = C C
-- cmd = O O
-- cstmt = O C
-- pat = C O

-- | For CMD, e: O=, C=there is a pattern

arrowParseMode :: E.ParseMode
arrowParseMode = E.defaultParseMode{E.extensions=[E.EnableExtension E.Arrows]}
parseArrow :: String -> E.ParseResult E.Exp
parseArrow = E.parseExpWithMode arrowParseMode

-- | A 'QuasiQuoter' that desugars proc-do notation and prepares for
-- CCA optimization via `arr'` and `init'` usage.
arrowInit :: QuasiQuoter
arrowInit = QuasiQuoter {
    quoteExp = \input -> case parseArrow input of
        E.ParseOk result -> desugarProc result >>= arrFixer
        E.ParseFailed l err -> error $ show l ++ show err
  , quotePat = error "cannot be patterns."
  , quoteDec = error "cannot be declarations."
  , quoteType = error "cannot be types."
  }
-- | A 'QuasiQuoter' that desugars proc-do notation.
arrow :: QuasiQuoter
arrow = arrowInit{
    quoteExp = \input -> case parseArrow input of
        E.ParseOk result -> desugarProc result
        E.ParseFailed l err -> error $ show l ++ show err}

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

type Stack = (Pat,[Pat])
(-:-) :: t -> (a, [a]) -> (t, [a])
s -:- (t,ss) = (s,t:ss)
(-::-) :: [a] -> (a, [a]) -> (a, [a])
[] -::- s = s
[s] -::- (t,ss) = (s,t:ss)
(p:ps) -::- (t,ss) = (p,ps ++ t:ss)

arrTH :: ExpQ -> ExpQ
arrTH = appE (varE $ mkName "arr")
(>:>) :: ExpQ -> ExpQ -> ExpQ
expr1 >:> expr2 = uInfixE expr1 (varE $ mkName ">>>") expr2
trim :: Stack -> Stack
trim (ConP _ [p],ps) = (p,ps)
trim (ConP _ (p:pss),ps) = (p,pss ++ ps)
trim (p,ps) = (p,ps)

trimAll :: Stack -> Stack
trimAll (p,ps) = (t,ts)
    where (t:ts) = map trimmer (p:ps)
trimmer :: Pat -> Pat
trimmer (ConP _ [pat]) = pat
trimmer p = p

tupleS :: Stack -> PatQ
tupleS (s,[]) = returnQ s
tupleS (s,ss) = returnQ $ TupP [s,TupP ss]

promoted :: Stack -> ExpQ
promoted (trim -> (s,ss)) = tupE $ map (returnQ . promote) $ (s:ss)

promote :: Pat -> Exp
promote (ConP _ [pat]) = promote pat
promote (ConP _ pats) = TupE $ map promote pats
promote (VarP n) = VarE n
promote (LitP n) = LitE n
promote (TupP pats) = TupE $ map promote pats
promote (ParensP pat) = ParensE $ promote pat
promote (ListP pats) = ListE $ map promote pats
promote (WildP) = TupE []
promote x = error $ "pattern promotion TODO" ++ show x

desugarProc :: E.Exp -> ExpQ
desugarProc (E.Proc _ (returnQ . toPat -> pat) (E.LeftArrApp (desugarProc -> expr1) (desugarProc -> expr2))) =
    [| arr $(lamE [pat] expr2) >>> $expr1 |] -- special case
desugarProc (E.Proc _ pat expr) = cmdToTH (toPat pat,[]) expr
desugarProc (E.Paren expr) = parensE $ desugarProc expr
desugarProc expr = returnQ $ toExp expr

cmdToTH :: Stack -> E.Exp -> ExpQ
cmdToTH stack (E.Proc _ (toPat -> pat) expr) = cmdToTH (pat -:- stack) expr --desugarProc p
cmdToTH stack (E.Do statements) = [| $(foldl1 (>:>) expressions) >>> arr fst |]
    where (_,expressions) = mapAccumL stmtToTH stack $ statements
cmdToTH stack (E.LeftArrApp (desugarProc -> expr) (desugarProc -> expr2)) =
    [| arr (\ $(tupleS stack) -> ($expr2,$(promoted stack))) >>> first $expr |]
cmdToTH stack expr = error $ "non-exaust: " ++ show stack ++ show expr

stmtToTH :: Stack -> E.Stmt -> (Stack,ExpQ)
stmtToTH stack (E.Qualifier expr) = --error $ (show $ stack) ++ (show expr)
                        ( WildP -:- trim stack, cmdToTH stack expr)
stmtToTH stack (E.Generator _ (toPat -> pat) expr) = (pat -:- trim stack,cmdToTH stack expr)
stmtToTH stack (E.LetStmt (E.BDecls d)) = (newStack,newExpression)
   where
      (newStack,exps) = mapAccumL process stack d
      newExpression = foldl1 (>:>) exps
      process s pbs@(E.PatBind _ (toPat -> pat) _ _ _) =
        ((pat -:- trim s),
            [| arr (\ $(tupleS s) ->
                      $(letE (map returnQ $ toDecs pbs)
                             (fmap promote $ tupleS (pat -:- trim s))
                       ) ) |] )
      process _ _ = error "Only pattern binds implemented"
stmtToTH _ (E.LetStmt _) = error "Only BDecls implemented for Let statements in stmtToTH"
stmtToTH stack (E.RecStmt statements) = (trimAll $ collectedPats -::- stack,exps)
    where
        exps = [| loop ( arr (\ ($(tupleS stack),$(returnQ $ TildeP $ TupP $ map trimmer collectedPats))
                              -> ($collectedExps,
                                  $(fmap promote $ tupleS $ trimAll stack)) )
                        >>> first $arrows
                        >>> arr (\ ($(returnQ $ TildeP $ tuplize TupP collectedPats),$(tupleS $ trimAll stack))
                                  -> ( $(fmap promote $ tupleS $ trimAll (collectedPats -::- stack)),
                                       $(returnQ $ TupE $ map (promote . trimmer) collectedPats)) ) )  -- should output, (newstack,collectedPats)
                                       |]

        (concat -> collectedPats,tuplize tupE . concat -> collectedExps) = unzip $ map collectRecData statements
        arrows = foldl1 (*:*) $ map collectArrows statements

-- | Backwards binary operator for use in stmtToTH.RecStmt
(*:*) :: ExpQ -> ExpQ -> ExpQ
y *:* x = [| first $x >>> arr (\(a,b)->(b,a)) >>> first $y >>> arr (\(a,b)->(b,a)) |] --used swapE

partitionStack :: [Pat] -> Pat
partitionStack [s] = s
partitionStack (s:ss) = TupP [s,TupP ss]
partitionStack _ = error "empty stack"

tuplize :: ([t] -> t) -> [t] -> t
tuplize _ [s] = s
tuplize t (s:ss) = t [s, tuplize t ss]
tuplize _ _ = error "no tuples"
collectRecData :: E.Stmt -> ([Pat], [ExpQ])
collectRecData (E.Generator _ (toPat -> pat) (E.LeftArrApp _ (desugarProc -> expr))) = ([pat],[expr])
collectRecData (E.Qualifier (E.LeftArrApp _ (desugarProc -> expr))) = ([WildP],[expr])
collectRecData (E.LetStmt (E.BDecls decls)) = (\(a,b) -> (a,b)) $ unzip $          -- uneeded id?
    map (\(E.PatBind _ (toPat -> p) _ (E.UnGuardedRhs (desugarProc -> rhs)) _) -> (p,rhs)) decls
collectRecData (E.RecStmt stmts) = (\(a,b) -> (concat a,concat b)) $ unzip $ map collectRecData stmts
collectRecData x = error $ "Error in collection of expressions: " ++ show x

collectArrows :: E.Stmt -> ExpQ
collectArrows (E.Generator _ _ (E.LeftArrApp exp1 _)) = desugarProc exp1   --normToExp undefined exp1 -- nested statments? UNDEFINED
collectArrows (E.Qualifier (E.LeftArrApp exp1 _)) = desugarProc exp1
collectArrows (E.LetStmt (E.BDecls _)) = [| arr id |] -- nested? no arrows inside let statments?
--collectArrows (E.RecStmt stmts) = _ $ map collectArrows stmts  nexted rec statements?
collectArrows x = error $ "Error in collections of arrows: " ++ show x

---}
---}
