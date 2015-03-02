{-# LANGUAGE TemplateHaskell #-}
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
dupArr l = app l (arrowE l) $ lamE l [charP l 'x'] $ tuple l [var l (name l "x"),var l (name l "x")]
sndArr l = app l (arrowE l) $ var l $ name l "snd"
fstArr l = app l (arrowE l) $ var l $ name l "fst"
arrowE l = var l $ name l "arr"
returnArr l = var l $ name l "returnA"
arrLambda l pats exp = App l (arrowE l) $ Lambda l [pTuple l pats] exp

arrowToExp :: (Eq l,SrcInfo l) => [S.Pat l] -> S.Exp l -> S.Exp l
arrowToExp pats (Proc l pattern exp) = arrowToExp (pattern:pats) exp
arrowToExp pats (LeftArrApp l exp exp2) = arrLambda l pats exp2 >:> exp
arrowToExp pats (Do l statements) = setup >:> helper statements >:> fstArr l
    where
        helper (s:[]) = arrowStmtToExp allpats s
        helper (s:ss) = arrowStmtToExp allpats s >:> correction allpats s >:> helper ss
        setup = arrLambda l pats $ Tuple l Boxed $ (promotePattern $ head allpats) :
                        (map (const $ Var l $ UnQual l $ name l "undefined")
                            $ tail allpats)
        allpats = pats ++ (collectPats statements)

arrowToExp pats (RightArrApp l exp exp2) = undefined
arrowToExp _ exp = exp

--arrowStmtToDec :: SrcInfo l => [Language.Haskell.Exts.Annotated.Pat l] -> Language.Haskell.Exts.Annotated.Stmt l -> Language.Haskell.Exts.Annotated.Exp l
correction pats (Generator l pattern exp) =
    arrLambda l [pTuple l [pattern],
                 pTuple l (replace pattern (PWildCard l) pats)]
                 $ promotePattern (PTuple l Boxed pats)
correction pats (Qualifier l exp) = sndArr l

arrowStmtToExp :: (Eq l,SrcInfo l) => [S.Pat l] -> S.Stmt l -> S.Exp l
arrowStmtToExp pats (Generator l pattern exp) = paren l ((paren l $ arrowToExp pats exp) &:& returnArr l)
arrowStmtToExp pats (Qualifier l exp) = paren l ((paren l $ arrowToExp pats exp) &:& returnArr l)
arrowStmtToExp _ _ = error "not implemented yet TODO"
--arrowStmtToExp pats (LetStmt l (BDecls l2 binds)) = arrLambda l pats _

collectPats ((Generator _ pattern _):rest) = pattern : collectPats rest
collectPats (_:rest) = collectPats rest
collectPats _ = []

promotePattern (PVar l name) = Var l (UnQual l name)
promotePattern (PTuple l b pats) = Tuple l b $ map promotePattern pats
promotePattern (PParen l pat) = Paren l $ promotePattern pat
promotePattern (PApp l qname pats) = Var l qname


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