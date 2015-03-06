{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ViewPatterns #-}
-- Thomas Bereknyei 2015
module Parser (arrowExp,arrowExpOpt,norm,normOpt) where
import Language.Haskell.Exts
import qualified Language.Haskell.Exts.Annotated.Syntax as S
import qualified Language.Haskell.Exts.Syntax as E
import Language.Haskell.Meta
import Language.Haskell.TH.Quote
import Language.Haskell.TH.Syntax
import qualified Language.Haskell.TH.Syntax as TH
import qualified Language.Haskell.TH.Lib as TH
import Language.Haskell.TH
import Data.List (mapAccumL)
import Debug.Trace
import Control.CCA
import qualified Control.CCA as C
import Control.CCA.CCNF
import Data.Generics.Uniplate.Data

arrowParseMode :: ParseMode
arrowParseMode = defaultParseMode{extensions=[EnableExtension Arrows]}
parseArrow :: String -> ParseResult (E.Exp )
parseArrow = parseExpWithMode arrowParseMode

arrowExp :: QuasiQuoter
arrowExp = QuasiQuoter {
    quoteExp = \input -> case parseArrow input of
        ParseOk result -> fromAExp $ normToExp [] $ h result -- norm $ AExp $ 
        --ParseOk result -> norm $ AExp $ normToExp [] $ h result
        ParseFailed l err -> error $ show l ++ show err
  , quotePat = error "cannot be patterns."
  , quoteDec = error "cannot be declarations."
  , quoteType = error "cannot be types."
  }
arrowExpOpt :: QuasiQuoter
arrowExpOpt = arrowExp{
    quoteExp = \input -> case parseArrow input of
        ParseOk result -> normOpt $ AExp $ normToExp [] $ h result
        ParseFailed l err -> error $ show l ++ show err
  }

normToExp :: [TH.Pat] -> E.Exp -> AExp
normToExp pats (E.Proc _ (toPat -> pattern) (h -> expr)) = normToExp (pattern:pats) expr
normToExp pats@(returnQ . TupP -> stack) (E.LeftArrApp (normToExp pats . h -> expr) (returnQ . toExp . h -> expr2)) =
    Arr [| (\ $stack -> $expr2) |] :>>> expr
normToExp pats (E.Do statements) =
    foldl1 (:>>>) expressions :>>> Arr [|fst|]
        where (_,expressions) = mapAccumL normStmt pats statements -- need stack for nexted do!
--normToExp _ (E.App (E.Var (E.UnQual (E.Ident "arr"))) b) = Arr $ returnQ $ toExp $ h b
normToExp _ (E.App (E.Var (E.UnQual (E.Ident "Arr"))) b) = Arr $ returnQ $ toExp $ h b
normToExp _ (E.App (E.Var (E.UnQual (E.Ident "Init"))) b) = Init $ returnQ $ toExp $ h b
--normToExp _ (E.UInfixE) = undefined
normToExp _ (E.Var (E.UnQual (E.Ident "returnA"))) = Arr [| id |] -- $ TH.dyn "id"
normToExp s (E.InfixApp (normToExp s . h -> leftExp) (E.QVarOp (E.UnQual (E.Symbol ">>>"))) (normToExp s . h -> rightExp) ) = leftExp :>>> rightExp -- $ TH.dyn "id"
normToExp _ expr = error $ "normToExp pattern fail  " ++ show expr

promoted stack = returnQ $ TupE $ map promote $ trim stack

normCmd :: [TH.Pat] -> E.Exp -> AExp
normCmd stack (E.LeftArrApp (normToExp stack . h -> expr) (returnQ . toExp . h -> expr2)) =
    Arr [| (\ $(returnQ $ listTup stack) -> ($expr2,$(promoted stack) )) |] :>>> (First expr)
normCmd _ _ = error "not imlemented, TODO"

normStmt :: [TH.Pat] -> E.Stmt -> ([TH.Pat],AExp)
normStmt stack (E.Generator _ (toPat -> pattern) (h -> expr)) = (pattern:trim stack,normCmd stack expr)
normStmt stack (E.Qualifier (h -> expr)) =                     (TH.WildP:trim stack,normCmd stack expr)
normStmt stack (E.LetStmt (E.BDecls [decls@(E.PatBind _ p _ _ _)])) = (toPat p:(trim stack),expression)
   where process binds@(E.PatBind l pat mtype rhs bs) = TH.LetE (toDecs binds) $ promote $ listTup (toPat pat:trim stack)
                                    --TupE ((promote $ toPat pat):(map promote $ trim stack))
         expression = Arr [| \ $(returnQ $ listTup stack) -> $(returnQ $ process decls) |]
normStmt stack (E.LetStmt (E.BDecls d@((decls@(E.PatBind _ p _ _ _)):ds) )) = (newStack,newExpression)
    where
          (newStack,exps) = mapAccumL normStmt stack (map (E.LetStmt . E.BDecls . return) d)
          newExpression = foldl1 (:>>>) exps
normStmt s@(returnQ . TupP -> stack) (E.RecStmt statements) = (trim $ collectedPats ++ s,exps)
    where
        exps = Loop ( Arr [| (\ ($stack,$(returnQ $ TildeP $TupP $ collectedPats))
                             -> ($(returnQ collectedExps) ,
                                 $(returnQ $ TupE $ map promote s)) ) |]
                     :>>> First arrows
                     :>>> Arr [| \($(returnQ $ TildeP $ tuplize TupP $ collectedPats),$(returnQ $ TupP $ trim s))
                                -> ( $(returnQ $ promote $ listTup $ trim (collectedPats ++ s)),
                                     $(returnQ $ TupE $ map promote collectedPats)) |] )  -- should output, (newstack,collectedPats)

        trimmedStack = trim s
        newPatterns = returnQ $ TupP $ collectedPats ++ s
        (map toPat . concat -> collectedPats,toExp . h . tuplize tuple . concat -> collectedExps) = unzip $ map collectRecData statements
        arrows = foldl1 (*:*) $ map collectArrows statements
x *:* y = First x :>>> Arr [| \(a,b)->(b,a) |] :>>> First y :>>> Arr [| \(a,b)->(b,a) |]
tuplize t [s] = s
tuplize t (s:ss) = t [s, tuplize t ss]

rend t [s] = t [s]
rend t (s:ss) = t [s,rend t ss]
rend t [] = t []

collectRecData (E.Generator _ pat (E.LeftArrApp exp1 expr)) = ([pat],[expr])
collectRecData (E.Qualifier (E.LeftArrApp exp1 expr)) = ([PWildCard],[expr])
collectRecData (E.LetStmt (E.BDecls decls)) = (\(a,b) -> (a,b)) $ unzip $ map (\(E.PatBind _ p _ (UnGuardedRhs rhs) _) -> (p,rhs)) decls
collectRecData (E.RecStmt stmts) = (\(a,b) -> (concat a,concat b)) $ unzip $ map collectRecData stmts
collectRecData x = error $ "Error in collection of expressions: " ++ show x

collectArrows (E.Generator _ _ (E.LeftArrApp exp1 _)) = normToExp undefined exp1 -- nested statments? UNDEFINED
collectArrows (E.Qualifier (E.LeftArrApp exp1 _)) = normToExp undefined exp1
collectArrows (E.LetStmt (E.BDecls decls)) = Arr [| id |] -- capture for arr'?
--collectArrows (E.RecStmt stmts) = _ $ map collectArrows stmts  nexted rec statements?
collectArrows x = error $ "Error in collections of arrows: " ++ show x

listTup [s] = TupP [s]
listTup (s:ss) = TupP [s,TupP ss]
listTup _ = error "empty stack"
arrFun = app (var (name "Arr"))
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
        arg x = Nothing

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
