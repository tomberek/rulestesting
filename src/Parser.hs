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
        ParseOk result -> norm $ AExp $ normToExp [] $ h result
        ParseFailed l err -> error $ show l ++ show err
  , quotePat = error "cannot be patterns."
  , quoteDec = error "cannot be declarations."
  , quoteType = error "cannot be types."
  }
arrowExpOpt :: QuasiQuoter
arrowExpOpt = QuasiQuoter {
    quoteExp = \input -> case parseArrow input of
        ParseOk result -> normOpt $ AExp $ normToExp [] $ h result
        ParseFailed l err -> error $ show l ++ show err
  , quotePat = error "cannot be patterns."
  , quoteDec = error "cannot be declarations."
  , quoteType = error "cannot be types."
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
--normToExp _ (E.UInfixE) = undefined
normToExp _ (E.Var (E.UnQual (E.Ident "returnA"))) = Arr [| id |] -- $ TH.dyn "id"
normToExp s (E.InfixApp (normToExp s . h -> leftExp) (E.QVarOp (E.UnQual (E.Symbol ">>>"))) (normToExp s . h -> rightExp) ) = leftExp :>>> rightExp -- $ TH.dyn "id"
normToExp _ expr = error $ "normToExp pattern fail  " ++ show expr

normStmt :: [TH.Pat] -> E.Stmt -> ([TH.Pat],AExp)
normStmt stack (E.Generator _ (toPat -> pattern) (h -> expr)) = (pattern:trim stack,normCmd stack expr)
normStmt stack (E.Qualifier (h -> expr)) =                     (TH.WildP:trim stack,normCmd stack expr)
normStmt stack (E.LetStmt (E.BDecls [decls@(E.PatBind _ p _ _ _)])) = (toPat p:(trim stack),expression)
   where process binds@(E.PatBind l pat mtype rhs bs) = TH.LetE (toDecs binds) $ TupE
                                               [(promote $ toPat pat),(TupE $ map promote $ trim stack)]
         expression = Arr [| \ $(returnQ $ listTup stack) -> $(returnQ $ process decls) |]
normStmt stack (E.LetStmt (E.BDecls d@((decls@(E.PatBind _ p _ _ _)):ds) )) = (newStack,newExpression)
    where
          (newStack,exps) = mapAccumL normStmt stack (map (E.LetStmt . E.BDecls . return) d)
          newExpression = foldl1 (:>>>) exps
normStmt s@(returnQ . TupP -> stack) (E.RecStmt statements) = (newStack,exps)
    where
        exps = Loop $ Arr [| (\ ($stack,$(returnQ $ TupP collectedPats)) 
                             -> ($(returnQ collectedExps),$(returnQ $ TupE $ map promote $ collectedPats ++ s) )) |] :>>> arrows :>>> Arr [| \x -> (x,x) |]
        newStack = collectedPats ++ s
        (map toPat -> collectedPats,toExp . h . rend -> collectedExps) = unzip $ map collectRecData statements
        arrows = foldl1 (*:*) $ map collectArrows statements
x *:* y = First x :>>> Arr [| \(a,b)->(b,a) |] :>>> First y :>>> Arr [| \(a,b)->(b,a) |]

rend [s] = tuple [s]
rend (s:ss) = tuple [s,rend ss]
rend [] = tuple []

collectRecData (E.Generator _ pat (E.LeftArrApp exp1 expr)) = (pat,expr)
collectRecData (E.Qualifier (E.LeftArrApp exp1 expr)) = (PWildCard,expr)
collectRecData (E.LetStmt (E.BDecls decls)) = (\(a,b) -> (pTuple a,tuple b)) $ unzip $ map (\(E.PatBind _ p _ (UnGuardedRhs rhs) _) -> (p,rhs)) decls
collectRecData (E.RecStmt stmts) = (\(a,b) -> (pTuple a,tuple b)) $ unzip $ map collectRecData stmts
collectRecData x = error $ "Error in collection of expressions: " ++ show x

collectArrows (E.Generator _ _ (E.LeftArrApp exp1 _)) = Arr $ returnQ $ toExp $ exp1
collectArrows (E.Qualifier (E.LeftArrApp exp1 _)) = Arr $ returnQ $ toExp $ exp1
collectArrows (E.LetStmt (E.BDecls decls)) = Arr [| id |] -- capture for arr'?
--collectArrows (E.RecStmt stmts) = _ $ map collectArrows stmts
collectArrows x = error $ "Error in collections of arrows: " ++ show x

promoted stack = returnQ $ TupE $ map promote $ trim stack

normCmd :: [TH.Pat] -> E.Exp -> AExp
normCmd stack (E.LeftArrApp (normToExp stack . h -> expr) (returnQ . toExp . h -> expr2)) =
    Arr [| (\ $(returnQ $ listTup stack) -> ($expr2,$(promoted stack) )) |] :>>> (First expr)
normCmd _ _ = error "not imlemented, TODO"

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
trim (WildP:p) = p
trim ((ConP _ p) :ps) = ((TupP p) : ps)
trim p = p

promote :: TH.Pat -> TH.Exp
promote (TH.ConP _ pats) = TupE $ map promote pats
promote (TH.VarP n) = VarE n
promote (TH.LitP n) = LitE n
promote (TH.TupP pats) = TupE $ map promote pats
promote (TH.ParensP pat) = ParensE $ promote pat
promote (TH.ListP pats) = ListE $ map promote pats
promote x = error $ "pattern promotion TODO" ++ show x
{-

l = norm
arrow :: QuasiQuoter
arrow = QuasiQuoter {
    quoteExp = \input -> case parseArrow input of
        ParseOk result -> undefined -- aToExp [] $ result
        ParseFailed l err -> error $ show l ++ show err
  , quotePat = error "cannot be patterns."
  , quoteDec = error "cannot be declarations."
  , quoteType = error "cannot be types."
  }
normStmt stack (E.LetStmt (E.BDecls [decls@(E.PatBind _ p _ _ _)])) = (toPat p:(trim stack),expression)
    where process binds@(E.PatBind l pat mtype rhs bs) = TH.LetE (toDecs binds) $ TupE
                                                [(promote $ toPat pat),(TupE $ map promote $ trim stack)]
          expression = [| $(C.arr [| \ $(stackTup $ stack) -> $(returnQ $ process decls)  |] ) |]
normStmt stack (E.LetStmt (E.BDecls d@((decls@(E.PatBind _ p _ _ _)):ds) )) = (newStack,newExpression)
    where
          expression = [| $(newExpression) |]
          (newStack,exps) = mapAccumL stmtToE stack (map (E.LetStmt . E.BDecls . return) d)
          newExpression = [| $(foldl1 next exps) |]
---}
{-
aToExp :: [TH.Pat] -> E.Exp -> TH.ExpQ
aToExp pats (E.Proc _ (toPat -> pattern) expr) = aToExp (pattern:pats) expr
aToExp pats@(returnQ . TupP -> stack) (E.LeftArrApp (aToExp pats -> expQ) (aToExp pats -> expr2)) = do
    let expr = expQ >>= replaceArr
    [| $(C.arr [|(\ $stack -> $expr2)|]) >>> $expr |]
aToExp pats (E.Do statements) =
    [| $(foldl1 next expressions) >>> $(C.arr [|fst|]) |]
        where (_,expressions) = mapAccumL stmtToE pats statements -- need stack for nexted do!
aToExp _ expr = returnQ $ toExp expr

replaceArr :: TH.Exp -> Q TH.Exp
replaceArr = transformM help
    where
        help (TH.AppE (TH.VarE (Name (OccName "arr") NameS)) b) = C.arr (returnQ b)
        help (TH.VarE (Name (OccName "returnA") NameS)) = C.arr [| id |]
        help x = returnQ x

stmtToE :: [TH.Pat] -> E.Stmt -> ([TH.Pat],TH.ExpQ)
stmtToE stack (E.Generator _ (toPat -> pattern) expr) = (pattern:trim stack,cmdToE stack expr)
stmtToE stack (E.Qualifier expr) =                     (TH.WildP:trim stack,cmdToE stack expr)
stmtToE stack (E.LetStmt (E.BDecls [decls@(E.PatBind _ p _ _ _)])) = (toPat p:(trim stack),expression)
    where process binds@(E.PatBind l pat mtype rhs bs) = TH.LetE (toDecs binds) $ TupE
                                                [(promote $ toPat pat),(TupE $ map promote $ trim stack)]
          expression = [| $(C.arr [| \ $(stackTup $ stack) -> $(returnQ $ process decls)  |] ) |]
stmtToE stack (E.LetStmt (E.BDecls d@((decls@(E.PatBind _ p _ _ _)):ds) )) = (newStack,newExpression)
    where
          expression = [| $(newExpression) |]
          (newStack,exps) = mapAccumL stmtToE stack (map (E.LetStmt . E.BDecls . return) d)
          newExpression = [| $(foldl1 next exps) |]

stmtToE _ _ = error "not implemented, TODO"

next x y = TH.uInfixE x (TH.dyn ">>>") y

stackTup stack = returnQ $ case stack of
                   [] -> error "empty stack"
                   [s] -> TupP [s]
                   (s:ss) -> TupP [s,TupP ss]

cmdToE :: [TH.Pat] -> E.Exp -> TH.ExpQ
cmdToE stack (E.LeftArrApp (aToExp stack -> expr) (aToExp stack -> expr2)) = do
    let expArr = expr >>= replaceArr
    [| $(C.arr [|(\ $(stackTup stack) -> ($expr2, $(promoted stack) )) |]) >>> $(TH.dyn "first") $expArr  |]

cmdToE _ _ = error "not imlemented, TODO"




{-
x >:> y = infixApp (ann x) x (op (ann y) $ name (ann y) ">>>") y
x &:& y = infixApp (ann x) x (op (ann y) $ name (ann y) "&&&") y
firstArr l x = app l (var l $ name l "first") x
dupArr l = app l (arrowE l) $ lamE l [pvar l $ name l "x"] $ tuple l [var l (name l "x"),var l (name l "x")]
dupEnv l = app l (arrowE l) $ lamE l [pTuple l [PWildCard l,pvar l $ name l "x"]] $ tuple l [var l (name l "x"),var l (name l "x")]
sndArr l = app l (arrowE l) $ var l $ name l "snd"
fstArr l = app l (arrowE l) $ var l $ name l "fst"
arrowE l = var l $ name l "arr"
returnArr l = var l $ name l "returnA"

arrLambda l [p] expr = App l2 (arrowE l2) $ Lambda l2 [PIrrPat l p] expr
    where l2 = ann expr
arrLambda l (p:pats) expr = App l2 (arrowE l2) $ Lambda l2 [pTuple l2 [PIrrPat l p,pTuple l2 $ map (PIrrPat l) pats]] expr
    where l2 = ann expr

arrowToExp :: (Show l,SrcInfo l,Eq l) => [S.Pat l] -> S.Exp l -> S.Exp l
arrowToexpr pats (Proc _ pattern (LeftArrApp l2 expr expr2)) = arrLambda l2 [pattern] expr2 >:> expr -- simplified or adds pattern + process
arrowToexpr pats (Proc _ pattern expr) = arrowToexpr (pattern:pats) expr
arrowToExp pats (Do l statements) = foldl1 (>:>) expressions >:> fstArr l
  where
      (env,expressions) = mapAccumL stmtToExp pats statements

--arrowToExp pats (RightArrApp l exp exp2) = undefined
arrowToExp _ exp = exp
stmtToExp :: (Show l,SrcInfo l,Eq l) => [S.Pat l] -> S.Stmt l -> ([S.Pat l],S.Exp l)
stmtToExp stack (Generator l pattern (arrowToExp stack -> expr)) = (pattern:trimStack stack,cmdToExp stack expr)
stmtToExp stack (Qualifier l (arrowToExp stack -> expr) )        = (pattern:trimStack stack,cmdToExp stack expr)
    where pattern = PWildCard l
--arrowStmtToExp pats (LetStmt l bs@(BDecls l2 decls)) = firstArr l $ arrLambda l pats (Let l bs
stmtToExp _ _ = error "statement to expression TODO"

cmdToExp stack (LeftArrApp l (arrowToExp stack -> exp) (arrowToExp stack -> exp2)) =  arrLambda l stack exp3 >:> firstArr l exp -- adds understanding of exp := arr (+2) <- 1 as arr (\_->1) >>> arr (+2)
 where
     exp3 = tuple (ann exp2) [exp2,tuple (ann exp2) $ map promotePattern $ trimStack stack]

trimStack ((PWildCard _):s) = s
trimStack s = s

promotePattern (PVar l name) = Var l (UnQual l name)
promotePattern (PTuple l b pats) = Tuple l b $ map promotePattern pats
promotePattern (PParen l pat) = Paren l $ promotePattern pat
promotePattern (PIrrPat _ pat) = promotePattern pat
promotePattern (PApp l qname pats) = appFun (repeat l) (Con l qname) $ map promotePattern pats
promotePattern (PList l pats) = List l $ map promotePattern pats
promotePattern _ = error "pattern promotion TODO"


{-
let tupleList = (n,(x,y))
let setup = arr (\n -> (n,undef,undef) )
let x = arr (\(n,(x,y)) -> n + n)  >>> id
let y = arr (\(n,x,y) -> x) >>> arr (+1)
let z = x+y -- binding
let r = arr (\(n,x,y) -> z) >>> returnA
let cleanup = arr ( \binding,tupleList -> tupleList with bindings)
let run = setup >>> ( x &&& id ) >>> arr ( \(x',(n,(x,y)) -> (n,(x',y))) ) 
loop $ (x &&& id) >>> cleanup >>= (y  &&& id) >>> cleanup


---}
{-
assocL :: (a,(b,c)) ~> ((a,b),c);
assocR :: ((a,b),c) ~> (a,(b,c); 
swap :: (a,b) ~> (b,a); 
unitL :: a ~> ((),a); 
retractL :: ((),a) ~> a; 
unitR :: a ~> (a,()); 
retractR :: (a,()) ~> a
--}
-- | From CGI
-- | Replaces all instances of a value in a list by another value.
replace :: Eq a =>
           a   -- ^ Value to look for
        -> a   -- ^ Value to replace it with
        -> [a] -- ^ Input list
        -> [a] -- ^ Output list
replace x y = map (\z -> if z == x then y else z)
--}
--}