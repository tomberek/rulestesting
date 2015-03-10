{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ViewPatterns #-}
-- Thomas Bereknyei 2015
module Control.Arrow.TH where
import qualified Language.Haskell.Exts as E
import Language.Haskell.Meta
import Language.Haskell.TH
import Language.Haskell.TH.Syntax

import Language.Haskell.TH.Quote
import Data.Generics.Uniplate.Operations
import Control.Arrow.Init
import Control.Arrow
import Control.Arrow.Init.Optimize
import Data.List (mapAccumL)


arrowParseMode :: E.ParseMode
arrowParseMode = E.defaultParseMode{E.extensions=[E.EnableExtension E.Arrows]}
parseArrow :: String -> E.ParseResult E.Exp
parseArrow = E.parseExpWithMode arrowParseMode

arrow :: QuasiQuoter
arrow = QuasiQuoter {
    quoteExp = \input -> case parseArrow input of
        E.ParseOk result -> desugarProc result >>= arrFixer
        --ParseOk result -> normToExp [] result
        E.ParseFailed l err -> error $ show l ++ show err
  , quotePat = error "cannot be patterns."
  , quoteDec = error "cannot be declarations."
  , quoteType = error "cannot be types."
  }
arrowTH :: QuasiQuoter
arrowTH = arrow{quoteExp = \input -> case parseArrow input of
    --E.ParseOk result -> desugarProc result >>= arrFixer
    E.ParseOk result ->  do
        f <- desugarProc result >>= arrFixer
        --error $ show f
        return f
    E.ParseFailed l err -> error $ show l ++ show err}

arrFixer :: Exp -> ExpQ
arrFixer = rewriteM arg
    where
        arg (AppE (VarE (Name (OccName "arr") _)) expr) =
            fmap Just [| arr' (returnQ $(lift expr)) $(returnQ expr) |]
        arg (AppE (VarE (Name (OccName "init") _)) expr) =
            fmap Just [| init' (returnQ $(lift expr)) $(returnQ expr) |]
        arg (VarE (Name (OccName "returnA") _)) =
            fmap Just [| arr' (returnQ $([| id |] >>= lift)) id |]
        {-arg (AppE (AppE (VarE (Name (OccName "loopD") _)) expr2) expr) =
              fmap Just [| loop (arr' (returnQ $(lift expr)) $(returnQ expr) >>>
                            second (init' (returnQ $(lift expr2)) $(returnQ expr2))) |]
        -}
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
    arrTH (lamE [pat] expr2) >:> expr1 -- special case
desugarProc (E.Proc _ pat expr) = cmdToTH (toPat pat,[]) expr
desugarProc (E.Paren expr) = parensE $ desugarProc expr
desugarProc expr = returnQ $ toExp expr

cmdToTH :: Stack -> E.Exp -> ExpQ
cmdToTH stack p@(E.Proc _ pat expr) = desugarProc p
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
y *:* x = [| first $x >>> arr $swapE >>> first $y >>> arr $swapE |]

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
