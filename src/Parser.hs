{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}
-- Thomas Bereknyei 2015
module Parser where
import Language.Haskell.Exts.Annotated
import qualified Language.Haskell.Exts.Annotated.Syntax as S
import qualified Language.Haskell.Exts.Syntax as E
import Language.Haskell.Exts.Annotated.Simplify
import Language.Haskell.Meta
import Language.Haskell.TH.Quote
import Language.Haskell.TH.Syntax
import qualified Language.Haskell.TH.Syntax as TH
import qualified Language.Haskell.TH.Lib as TH
import Data.List (intercalate,mapAccumL)
import Debug.Trace
import Control.Arrow(arr,(>>>))
import qualified Control.CCA as C

arrowParseMode = defaultParseMode{extensions=[EnableExtension Arrows]}
parseArrow = parseExpWithMode arrowParseMode

arrow = QuasiQuoter {
    quoteExp = \input -> case parseArrow input of
        ParseOk result -> aToExp [] $ sExp result
        --ParseOk result -> returnQ $ toExp $ sExp $ arrowToExp [] result
        ParseFailed loc err -> error $ show loc ++ show err
  , quotePat = error "cannot be patterns."
  , quoteDec = error "cannot be declarations."
  , quoteType = error "cannot be types."
  }


next x y = TH.uInfixE x (TH.dyn ">>>") y
n = TH.infixE Nothing (TH.dyn ">>>") Nothing
aToExp :: [TH.Pat] -> E.Exp -> TH.ExpQ
aToExp pats (E.Proc l (toPat -> pattern) exp) = aToExp (pattern:pats) exp
aToExp pats (E.LeftArrApp (aToExp pats -> exp) (aToExp pats -> exp2)) = [| $(C.arr [|(\ $(returnQ $ TupP pats) -> $exp2)|]) >>> $exp |]
aToExp pats (E.Do statements) =
    [| $(foldl1 next expressions) >>> $(C.arr [|fst|]) |]
        where (env,expressions) = mapAccumL stmtToE pats statements
aToExp pats exp = returnQ $ toExp exp

stmtToE :: [TH.Pat] -> E.Stmt -> ([TH.Pat],TH.ExpQ)
stmtToE stack (E.Generator l (toPat -> pattern) exp) = (pattern:trim stack,cmdToE stack exp)
stmtToE stack (E.Qualifier exp) =                     (TH.WildP:trim stack,cmdToE stack exp)
stmtToE _ _ = error "not implemented, TODO"

cmdToE :: [TH.Pat] -> E.Exp -> TH.ExpQ
cmdToE stack@(s:ss) (E.LeftArrApp (aToExp stack -> exp) (aToExp stack -> exp2))
    = [| $(C.arr [|(\ $stack' -> ($exp2, $(returnQ $ TupE $ map promote $ trim stack) )) |]) >>> $firstE $exp  |]
               where stack' = returnQ $ case stack of
                                          [s] -> TupP [s]
                                          (s:ss) -> TupP [s,TupP ss]
cmdToE _ _ = error "not imlemented, TODO"

arrE = TH.dyn "arr"
firstE = TH.dyn "first"

trim (WildP:p) = p
trim ((ConP _ p) :ps) = ((TupP p) : ps)
trim p = p
viewP :: ToPat a => a -> TH.PatQ
viewP = returnQ . toPat

promote (TH.ConP _ pats) = TupE $ map promote pats
promote (TH.VarP name) = VarE name
promote (TH.LitP name) = LitE name
promote (TH.TupP pats) = TupE $ map promote pats
promote (TH.ParensP pat) = ParensE $ promote pat
promote (TH.ListP pats) = ListE $ map promote pats
promote x = error $ "pattern promotion TODO" ++ show x

x >:> y = infixApp (ann x) x (op (ann y) $ name (ann y) ">>>") y
x &:& y = infixApp (ann x) x (op (ann y) $ name (ann y) "&&&") y
firstArr l x = app l (var l $ name l "first") x
dupArr l = app l (arrowE l) $ lamE l [pvar l $ name l "x"] $ tuple l [var l (name l "x"),var l (name l "x")]
dupEnv l = app l (arrowE l) $ lamE l [pTuple l [PWildCard l,pvar l $ name l "x"]] $ tuple l [var l (name l "x"),var l (name l "x")]
sndArr l = app l (arrowE l) $ var l $ name l "snd"
fstArr l = app l (arrowE l) $ var l $ name l "fst"
arrowE l = var l $ name l "arr"
returnArr l = var l $ name l "returnA"

arrLambda l [p] exp = App l2 (arrowE l2) $ Lambda l2 [PIrrPat l p] exp
    where l2 = ann exp
arrLambda l (p:pats) exp = App l2 (arrowE l2) $ Lambda l2 [pTuple l2 [PIrrPat l p,pTuple l2 $ map (PIrrPat l) pats]] exp
    where l2 = ann exp

arrowToExp :: (Show l,SrcInfo l,Eq l) => [S.Pat l] -> S.Exp l -> S.Exp l
arrowToExp pats (Proc l pattern (LeftArrApp l2 exp exp2)) = arrLambda l2 [pattern] exp2 >:> exp -- simplified or adds pattern + process
arrowToExp pats (Proc l pattern exp) = arrowToExp (pattern:pats) exp
arrowToExp pats (Do l statements) = foldl1 (>:>) expressions >:> fstArr l
  where
      (env,expressions) = mapAccumL stmtToExp pats statements

--arrowToExp pats (RightArrApp l exp exp2) = undefined
arrowToExp _ exp = exp
stmtToExp :: (Show l,SrcInfo l,Eq l) => [S.Pat l] -> S.Stmt l -> ([S.Pat l],S.Exp l)
stmtToExp stack (Generator l pattern (arrowToExp stack -> exp)) = (pattern:trimStack stack,cmdToExp stack exp)
stmtToExp stack (Qualifier l (arrowToExp stack -> exp) )        = (pattern:trimStack stack,cmdToExp stack exp)
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
promotePattern (PIrrPat l pat) = promotePattern pat
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