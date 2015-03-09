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
import Control.Arrow.Init.Optimize
import Data.Generics.Uniplate.Operations
import Debug.Trace (trace)

arrowParseMode :: E.ParseMode
arrowParseMode = E.defaultParseMode{E.extensions=[E.EnableExtension E.Arrows]}
parseArrow :: String -> E.ParseResult E.Exp
parseArrow = E.parseExpWithMode arrowParseMode

arrow :: QuasiQuoter
arrow = QuasiQuoter {
    quoteExp = \input -> case parseArrow input of
        E.ParseOk result -> procExp result
        --ParseOk result -> normToExp [] result
        E.ParseFailed l err -> error $ show l ++ show err
  , quotePat = error "cannot be patterns."
  , quoteDec = error "cannot be declarations."
  , quoteType = error "cannot be types."
  }
arrowTest = arrow{quoteExp = \input -> case parseArrow input of
        E.ParseOk result -> returnQ $ toExp $ thApp "returnQ" $ g result
        E.ParseFailed l err -> error $ show l ++ show err}

type Stack = (Pat,[Pat])
s -:- (t,ss) = (s,t:ss)

arrTH :: Q Exp -> Q Exp
arrTH expr = appE (varE $ mkName "arr") expr
(>:>) :: Q Exp -> Q Exp -> Q Exp
expr1 >:> expr2 = uInfixE expr1 (varE $ mkName ">>>") expr2
l = norm
t = lowerTH
procExp :: E.Exp -> Q Exp
procExp (E.Proc _ (returnQ . toPat -> pat) (E.LeftArrApp (returnQ . toExp -> expr1) (returnQ . toExp -> expr2))) =
    arrTH (lamE [pat] expr2) >:> [| fmap lowerTH $ norm $(expr1) |] -- special case
procExp (E.Proc _ pat expr) = cmdToTH (toPat pat,[]) expr
procExp expr = returnQ $ toExp expr

cmdToTH :: Stack -> E.Exp -> Q Exp
cmdToTH stack (E.LeftArrApp expr expr2) = [| normE $(returnQ $ toExp expr) |]

arrFun :: E.Exp -> E.Exp
arrFun x = E.appFun (E.var (E.name "Exp")) undefined

thApp x y = E.App (E.Var $ E.Qual (E.ModuleName "Language.Haskell.TH.Syntax") (E.Ident x)) y
thConSyntaxE x y = E.App (E.Con $ E.Qual (E.ModuleName "Language.Haskell.TH.Syntax") (E.Ident x)) y
thConE x y = E.App (E.Con $ E.Qual (E.ModuleName "Language.Haskell.TH") (E.Ident x)) y
thCon x = E.Con $ E.Qual (E.ModuleName "Language.Haskell.TH") (E.Ident x)
thConSyntax x = E.Con $ E.Qual (E.ModuleName "Language.Haskell.TH.Syntax") (E.Ident x)
th x = E.Var $ E.Qual (E.ModuleName "Language.Haskell.TH") (E.Ident x)
thVarE x = thConE "VarE" x
thVarP x = thApp "VarP" x
thParensP x = thApp "ParensP" x
thTupP x = thApp "TupP" x
thTupE x = thConE "TupE" $ E.List x
tha = NameS
thName (E.Ident string) = E.appFun (thConSyntax "Name") [(E.App (thConSyntax "OccName")
                    $ E.strE string), thConSyntax "NameS"]

patToExts :: E.Pat -> E.Exp
patToExts (E.PVar name) = thConE "VarP" $ thName name

test (E.Var (E.UnQual name)) = thVarE $ thName name
test (E.Tuple E.Boxed exps) = thTupE $ map test exps
test (E.Lambda _ pats exp) = E.appFun (thCon "LamE") [E.List $ map patToExts pats,test exp]

                                  --  [pat] exp
g :: E.Exp -> E.Exp
g = rewrite arg
    where
        arg l@(E.Lambda _ _ _) = Just $ test l
        arg _ = Nothing

h :: E.Exp -> E.Exp
h = rewrite arg
    where
        arg (E.App (E.Var (E.UnQual (E.Ident "arr"))) b) = Just $ arrFun b
        arg (E.App (E.Var (E.UnQual (E.Symbol "arr"))) b) = Just $ arrFun b
        arg (E.App (E.Var (E.Qual _ (E.Symbol "arr"))) b) = Just $ arrFun b
        arg (E.App (E.Var (E.Qual _ (E.Ident "arr"))) b) = Just $ arrFun b
        arg (E.App (E.Var (E.UnQual (E.Ident "init"))) b) = Just $ E.app (E.var (E.name "Init")) b
        arg (E.App (E.Var (E.UnQual (E.Symbol "init"))) b) = Just $ E.app (E.var (E.name "Init")) b
        arg (E.App (E.Var (E.Qual _ (E.Symbol "init"))) b) = Just $ E.app (E.var (E.name "Init")) b
        arg (E.App (E.Var (E.Qual _ (E.Ident "init"))) b) = Just $ E.app (E.var (E.name "Init")) b
        arg (E.Var (E.UnQual (E.Ident "returnA"))) = Just $ arrFun (E.var $ E.name "id")
        arg (E.Var (E.UnQual (E.Symbol "returnA"))) = Just $ arrFun (E.var $ E.name "id")
        arg (E.Var (E.Qual _ (E.Ident "returnA"))) = Just $ arrFun (E.var $ E.name "id")
        arg (E.Var (E.Qual _ (E.Symbol "returnA"))) = Just $ arrFun (E.var $ E.name "id")
        --arg (E.InfixApp leftExp (E.QVarOp (E.UnQual (E.Symbol ">>>"))) rightExp ) = Just $ infixApp leftExp (op $ name ":>>>") rightExp
        --arg (E.InfixApp leftExp (E.QVarOp (E.UnQual (E.Symbol "<<<"))) rightExp ) = Just $ infixApp rightExp (op $ name ":>>>") leftExp
        --arg (E.InfixApp leftExp (E.QVarOp (E.UnQual (E.Symbol "***"))) rightExp ) = Just $ infixApp leftExp (op $ name ":***") rightExp
        arg _ = Nothing

{-
normToExp :: [TH.Pat] -> E.Exp -> TH.Exp
normToExp pats (E.Proc _ (toPat -> pattern) expr) = normToExp (pattern:pats) expr
--normToExp pats (E.Proc _ (toPat -> pattern) (h -> expr)) = error $ "TOM: " ++ show expr
normToExp pats (E.LeftArrApp e@(normToExp pats -> expr) (returnQ . toExp -> expr2)) = let expr3 = [| normE $(returnQ $ toExp e) |] in
    Arr [| (\ $(returnQ $ TupP pats) -> $expr2) |] :>>> expr
normToExp pats (E.Do statements) =
    foldl1 (:>>>) expressions :>>> Arr [|fst|]
        where (_,expressions) = mapAccumL normStmt pats statements -- need stack for nexted do!
normToExp _ (E.App (E.Var (E.UnQual (E.Ident "Arr"))) b) = Arr $ returnQ $ toExp  b
normToExp _ (E.App (E.Var (E.UnQual (E.Ident "Init"))) b) = Init $ returnQ $ toExp b
normToExp s (E.InfixApp (normToExp s -> leftExp) (E.QVarOp (E.UnQual (E.Ident ":>>>"))) (normToExp s -> rightExp) ) = normalize $ leftExp :>>> rightExp
normToExp s (E.InfixApp (normToExp s -> leftExp) (E.QVarOp (E.UnQual (E.Ident ":***"))) (normToExp s -> rightExp) ) = normalize $ leftExp :*** rightExp
--normToExp _ (E.Var (E.UnQual (E.Ident "returnA"))) = Arr [| id |]
--normToExp s (E.InfixApp (normToExp s -> leftExp) (E.QVarOp (E.UnQual (E.Symbol "<<<"))) (normToExp s -> rightExp) ) = rightExp :>>> leftExp
--normToExp s (E.InfixApp (normToExp s -> leftExp) (E.QVarOp (E.UnQual (E.Symbol "***"))) (normToExp s -> rightExp) ) = rightExp :>>> leftExp
--normToExp _ expr = error "normToExp fail"
normToExp _ expr = Debug.Trace.trace "normToExp pattern fail" $ Expr $ returnQ $ toExp $ expr

promoted :: [TH.Pat] -> Q TH.Exp
promoted stack = returnQ $ TupE $ map promote $ trim stack

normCmd :: [TH.Pat] -> E.Exp -> AExp
normCmd stack (E.LeftArrApp (normToExp stack . h -> expr) (returnQ . toExp -> expr2)) =
    Arr [| (\ $(returnQ $ partitionStack stack) -> ($expr2,$(promoted stack) )) |] :>>> (First expr)
normCmd _ _ = error "not imlemented, TODO"

temp :: ArrowInit a => E.Exp -> Q (TH.TExp (a Int Int))
temp f = [|| $$(returnQ $ TExp $ toExp f) ||]
temp2 :: E.Exp -> Q (TH.TExp (A.Arr f m Int Int))
temp2 f = temp f
temp3 :: E.Exp -> Q (TH.Exp)
temp3 f = unTypeQ $ temp2 f
norm1 (AExp f) = norm f


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
---}
---}
---}

