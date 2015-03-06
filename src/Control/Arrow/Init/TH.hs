{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ViewPatterns #-}
-- Thomas Bereknyei 2015
module Control.Arrow.Init.TH (arrow,arrowOpt,norm,normOpt,ArrowInit(..)) where
import Language.Haskell.Exts
import qualified Language.Haskell.Exts.Syntax as E
import Language.Haskell.Meta
import Language.Haskell.TH.Quote
import Language.Haskell.TH.Syntax
import qualified Language.Haskell.TH.Syntax as TH
import Data.List (mapAccumL)
import Control.Arrow.Init.Optimize
import Data.Generics.Uniplate.Data

arrowParseMode :: ParseMode
arrowParseMode = defaultParseMode{extensions=[EnableExtension Arrows]}
parseArrow :: String -> ParseResult (E.Exp )
parseArrow = parseExpWithMode arrowParseMode

arrow :: QuasiQuoter
arrow = QuasiQuoter {
    quoteExp = \input -> case parseArrow input of
        ParseOk result -> fromAExp $ normToExp [] $ h result
        --ParseOk result -> norm $ normToExp [] $ h result
        ParseFailed l err -> error $ show l ++ show err
  , quotePat = error "cannot be patterns."
  , quoteDec = error "cannot be declarations."
  , quoteType = error "cannot be types."
  }
arrowOpt :: QuasiQuoter
arrowOpt = arrow{
    quoteExp = \input -> case parseArrow input of
        ParseOk result -> normOpt $ normToExp [] $ h result
        ParseFailed l err -> error $ show l ++ show err
  }

normToExp :: [TH.Pat] -> E.Exp -> AExp
normToExp pats (E.Proc _ (toPat -> pattern) (h -> expr)) = normToExp (pattern:pats) expr
normToExp pats (E.LeftArrApp (normToExp pats -> expr) (returnQ . toExp -> expr2)) =
    Arr [| (\ $(returnQ $ TupP pats) -> $expr2) |] :>>> expr
normToExp pats (E.Do statements) =
    foldl1 (:>>>) expressions :>>> Arr [|fst|]
        where (_,expressions) = mapAccumL normStmt pats statements -- need stack for nexted do!
normToExp _ (E.App (E.Var (E.UnQual (E.Ident "Arr"))) b) = Arr $ returnQ $ toExp  b
normToExp _ (E.App (E.Var (E.UnQual (E.Ident "Init"))) b) = Init $ returnQ $ toExp b
normToExp _ (E.Var (E.UnQual (E.Ident "returnA"))) = Arr [| id |]
normToExp s (E.InfixApp (normToExp s -> leftExp) (E.QVarOp (E.UnQual (E.Symbol ">>>"))) (normToExp s -> rightExp) ) = leftExp :>>> rightExp
normToExp s (E.InfixApp (normToExp s -> leftExp) (E.QVarOp (E.UnQual (E.Symbol "<<<"))) (normToExp s -> rightExp) ) = rightExp :>>> leftExp
normToExp s (E.InfixApp (normToExp s -> leftExp) (E.QVarOp (E.UnQual (E.Symbol "***"))) (normToExp s -> rightExp) ) = rightExp :>>> leftExp
normToExp _ expr = error $ "normToExp pattern fail  " ++ show expr

promoted :: [TH.Pat] -> Q TH.Exp
promoted stack = returnQ $ TupE $ map promote $ trim stack

normCmd :: [TH.Pat] -> E.Exp -> AExp
normCmd stack (E.LeftArrApp (normToExp stack -> expr) (returnQ . toExp -> expr2)) =
    Arr [| (\ $(returnQ $ partitionStack stack) -> ($expr2,$(promoted stack) )) |] :>>> (First expr)
normCmd _ _ = error "not imlemented, TODO"

normStmt :: [TH.Pat] -> E.Stmt -> ([TH.Pat],AExp)
normStmt stack (E.Generator _ (toPat -> pattern) (h -> expr)) = (pattern:trim stack,normCmd stack expr)
normStmt stack (E.Qualifier (h -> expr)) =                     (TH.WildP:trim stack,normCmd stack expr)
normStmt stack (E.LetStmt (E.BDecls [decls@(E.PatBind _ p _ _ _)])) = (toPat p:(trim stack),expression)
   where
       process pbs@(E.PatBind _ pat _ _ _) = TH.LetE (toDecs pbs) $ promote $ partitionStack (toPat pat:trim stack)
       process _ = error "Only pattern binds implemented"
       expression = Arr [| \ $(returnQ $ partitionStack stack) -> $(returnQ $ process decls) |]
normStmt stack (E.LetStmt (E.BDecls d@( (E.PatBind _ _ _ _ _):_) )) = (newStack,newExpression)
    where
          (newStack,exps) = mapAccumL normStmt stack (map (E.LetStmt . E.BDecls . return) d)
          newExpression = foldl1 (:>>>) exps
normStmt s (E.RecStmt statements) = (trim $ collectedPats ++ s,exps)
    where
        exps = Loop ( Arr [| (\ ($(tupPQ s),$(returnQ $ TildeP $TupP $ collectedPats))
                             -> ($(returnQ collectedExps) ,
                                 $(tupEQ $ map promote s)) ) |]
                     :>>> First arrows
                     :>>> Arr [| \($(returnQ $ TildeP $ tuplize TupP $ collectedPats),$(tupPQ $ trim s))
                                -> ( $(returnQ $ promote $ partitionStack $ trim (collectedPats ++ s)),
                                     $(tupEQ $ map promote collectedPats)) |] )  -- should output, (newstack,collectedPats)

        (map toPat . concat -> collectedPats,toExp . tuplize tuple . concat -> collectedExps) = unzip $ map collectRecData statements
        arrows = foldr1 (*:*) $ map collectArrows statements
normStmt _ statement = error $ "not implemented: " ++ show statement
(*:*) :: AExp -> AExp -> AExp
x *:* y = First x :>>> Arr swapE :>>> First y :>>> Arr swapE

tupEQ :: [TH.Exp] -> Q TH.Exp
tupEQ = returnQ . TupE
tupPQ :: [TH.Pat] -> Q TH.Pat
tupPQ = returnQ . TupP

partitionStack :: [TH.Pat] -> TH.Pat
partitionStack [s] = s
partitionStack (s:ss) = TupP [s,TupP ss]
partitionStack _ = error "empty stack"

tuplize :: ([t] -> t) -> [t] -> t
tuplize _ [s] = s
tuplize t (s:ss) = t [s, tuplize t ss]
tuplize _ _ = error "no tuples"

collectRecData :: E.Stmt -> ([E.Pat], [E.Exp])
collectRecData (E.Generator _ pat (E.LeftArrApp _ expr)) = ([pat],[expr])
collectRecData (E.Qualifier (E.LeftArrApp _ expr)) = ([PWildCard],[expr])
collectRecData (E.LetStmt (E.BDecls decls)) = (\(a,b) -> (a,b)) $ unzip $ map (\(E.PatBind _ p _ (UnGuardedRhs rhs) _) -> (p,rhs)) decls
collectRecData (E.RecStmt stmts) = (\(a,b) -> (concat a,concat b)) $ unzip $ map collectRecData stmts
collectRecData x = error $ "Error in collection of expressions: " ++ show x

collectArrows :: E.Stmt -> AExp
collectArrows (E.Generator _ _ (E.LeftArrApp exp1 _)) = normToExp undefined exp1 -- nested statments? UNDEFINED
collectArrows (E.Qualifier (E.LeftArrApp exp1 _)) = normToExp undefined exp1
collectArrows (E.LetStmt (E.BDecls _)) = Arr [| id |] -- nested? no arrows inside let statments?
--collectArrows (E.RecStmt stmts) = _ $ map collectArrows stmts  nexted rec statements?
collectArrows x = error $ "Error in collections of arrows: " ++ show x

arrFun :: E.Exp -> E.Exp
arrFun = app (var (name "Arr"))

h :: E.Exp -> E.Exp
h = rewrite arg
    where
        arg (E.App (E.Var (E.UnQual (E.Ident "arr"))) b) = Just $ arrFun b
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
        arg _ = Nothing

trim :: [TH.Pat] -> [TH.Pat]
trim ((ConP _ p) :ps) = (p ++ ps)
trim (p:ps) = p:trim ps
trim p = p

promote :: TH.Pat -> TH.Exp
promote (TH.ConP _ [pat]) = promote pat
promote (TH.ConP _ pats) = TupE $ map promote pats
promote (TH.VarP n) = VarE n
promote (TH.LitP n) = LitE n
promote (TH.TupP pats) = TupE $ map promote pats
promote (TH.ParensP pat) = ParensE $ promote pat
promote (TH.ListP pats) = ListE $ map promote pats
promote (TH.WildP) = TupE []
promote x = error $ "pattern promotion TODO" ++ show x

---}
