{-# LANGUAGE TemplateHaskell #-}
-- Thomas Bereknyei 2015
module Parser where
import Language.Haskell.Exts.Annotated
import qualified Language.Haskell.Exts.Annotated.Syntax as S
import Language.Haskell.Exts.Annotated.Simplify
import Language.Haskell.Meta
import Language.Haskell.TH.Quote
import Language.Haskell.TH.Syntax
import Data.List (intercalate)
import Debug.Trace
import Control.Arrow(arr)

arrowParseMode = defaultParseMode{extensions=[EnableExtension Arrows]}
parseArrow = parseExpWithMode arrowParseMode

arrow = QuasiQuoter {
    quoteExp = \input -> case parseArrow input of
        ParseOk result -> returnQ $ toExp $ sExp $ arrowToExp [] result
        ParseFailed loc err -> error $ show loc ++ show err
  , quotePat = error "cannot be patterns."
  , quoteDec = error "cannot be declarations."
  , quoteType = error "cannot be types."
  }

x >:> y = infixApp (ann x) x (op (ann x) $ name (ann x) ">>>") y
x &:& y = infixApp (ann x) x (op (ann x) $ name (ann x) "&&&") y
firstArr l x = app l (var l $ name l "first") x
dupArr l = app l (arrowE l) $ lamE l [pvar l $ name l "x"] $ tuple l [var l (name l "x"),var l (name l "x")]
sndArr l = app l (arrowE l) $ var l $ name l "snd"
fstArr l = app l (arrowE l) $ var l $ name l "fst"
arrowE l = var l $ name l "arr"
returnArr l = var l $ name l "returnA"
arrLambda l pats exp = App l (arrowE l) $ Lambda l [pTuple l $ map (PIrrPat l) pats] exp

arrowToExp :: (Show l,Eq l,SrcInfo l) => [S.Pat l] -> S.Exp l -> S.Exp l
arrowToExp pats (Proc l pattern exp) = arrowToExp (pattern:pats) exp
arrowToExp pats (LeftArrApp l exp exp2) = arrLambda l pats exp2 >:> exp
arrowToExp pats (Do l statements) = setup >:> dupArr l >:> helper statements >:> fstArr l
    where
        helper (s:[]) = arrowStmtToExp allpats s
        helper (s:ss) = arrowStmtToExp allpats s >:> correction allpats s >:> helper ss
        setup = arrLambda l pats $ Tuple l Boxed $ (promotePattern $ head allpats) :
                        (map (const $ app l (Var l $ UnQual l $ name l "error") (strE l $ "variable not defined at " ++ (show $ getPointLoc l)) )
                            $ tail allpats)
        allpats = pats ++ (collectPats statements)

--arrowToExp pats (RightArrApp l exp exp2) = undefined
arrowToExp _ exp = exp

correction pats (Generator l pattern exp) =
    arrLambda l [pTuple l [pattern],
                 pTuple l (replace pattern (PWildCard l) pats)]
                 (promotePattern (PTuple l Boxed pats)) >:> dupArr l
correction pats (Qualifier l exp) = sndArr l >:> dupArr l

arrowStmtToExp :: (Show l,Eq l,SrcInfo l) => [S.Pat l] -> S.Stmt l -> S.Exp l
arrowStmtToExp pats (Generator l pattern exp) = firstArr l $ arrowToExp pats exp
arrowStmtToExp pats (Qualifier l exp) = firstArr l $ arrowToExp pats exp
--arrowStmtToExp pats (LetStmt l bs@(BDecls l2 decls)) = firstArr l $ arrLambda l pats (Let l bs
arrowStmtToExp _ _ = error "not implemented yet TODO"

collectPats ((Generator _ pattern _):rest) = pattern : collectPats rest
collectPats (_:rest) = collectPats rest
collectPats _ = []

promotePattern (PVar l name) = Var l (UnQual l name)
promotePattern (PTuple l b pats) = Tuple l b $ map promotePattern pats
promotePattern (PParen l pat) = Paren l $ promotePattern pat
promotePattern (PIrrPat l pat) = promotePattern pat
promotePattern (PApp l qname pats) = appFun (repeat l) (Con l qname) $ map promotePattern pats
promotePattern (PList l pats) = List l $ map promotePattern pats
promotePattern (PWildCard l) = var l $ name l "undefined"


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