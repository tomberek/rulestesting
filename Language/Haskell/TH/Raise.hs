{-# LANGUAGE TemplateHaskell #-}
module Language.Haskell.TH.Raise where
import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Syntax (returnQ)
import Language.Haskell.Meta
raiseP x = [| x |]
raisePat :: Pat -> ExpQ
raisePat (LitP lit) = [| LitP lit |]
raisePat (VarP name) = [| VarP name |]
raisePat (TupP pats) = [| TupP pats |]
raisePat (UnboxedTupP pats) = [| UnboxedTupP $(raise pats) |]
raisePat (ConP name pats) = [| ConP name $(raise pats) |]
raisePat (InfixP pat name pat2) = [| InfixP $(raise pat) name $(raise pat2) |]
raisePat (UInfixP pat name pat2) = [| UInfixP $(raise pat) name $(raise pat2) |]
raisePat (ParensP pat) = [| ParensP $(raise pat) |]
raisePat (TildeP pat) = [| TildeP $(raise pat) |]
raisePat (BangP pat) = [| BangP $(raise pat) |]
raisePat (AsP name pat) = [| AsP name $(raise pat) |]
raisePat (WildP) = [| WildP |]
raisePat (RecP name fieldpats) = [| RecP name $(listE $ map (\(a,b) -> tupE [ [|a|],raise b]) fieldpats) |]
raisePat (ListP pats) = [| ListP $(raise pats) |]
raisePat (SigP pat typ) = [| SigP $(raise pat) $(raise typ) |]
raisePat (ViewP expr pat) = [| ViewP $(raise expr) $(raise pat) |]

-- | Like Lift, but lifts even higher creating a TH representation of a TH representation of `t`
raiseHigher (LitP lit) = [|| LitP lit ||]
class Raise t where
    raise :: t -> ExpQ
instance Raise Pat where raise = lift
instance Raise Exp where raise = raiseExp
instance Raise Type where raise = raiseType
instance Raise Dec where raise = raiseDec
instance Raise a => Raise [a] where raise r = mapM raise r >>= returnQ . ListE
raiseExp :: Exp -> ExpQ
raiseExp (VarE name) = [| VarE name |]
raiseExp (ConE name) = [| ConE name |]
raiseExp (LitE lit) = [| LitE lit |]
raiseExp (AppE expr expr2) = [| AppE $(raise expr) $(raise expr2) |]
raiseExp (InfixE expr expr2 expr3) = [| InfixE $(maybe [|Nothing|] (appE [|Just|] . raise) expr)
                                        $(raise expr2)
                                        $(maybe [|Nothing|] (appE [|Just|] . raise) expr3) |]
raiseExp (UInfixE expr3 expr mexpr2) = [| UInfixE $(raise expr3) $(raise expr) $(raise mexpr2) |]
raiseExp (ParensE expr) = [| ParensE $(raise expr) |]
raiseExp (LamE pats expr) = [| LamE $(raise pats) $(raise expr) |]
raiseExp (LamCaseE matches) = error "LamCaseE not implemented"
raiseExp (TupE exps) = [| TupE $(raise exps) |]
raiseExp (ListE exps) = [| ListE $(raise exps) |]
raiseExp (LetE decs expr) = [| LetE $(raise decs) $(raise expr) |]
raiseExp (SigE expr typ) = [| SigE $(raise expr) $(raise typ) |]
raiseExp x = error $ "func f: " ++ show x

raiseDec (ValD pat (NormalB bexp) decs) = [| ValD $(raise pat) (NormalB $ $(raise bexp)) $(raise decs) |]
raiseDec _ = error "partial raiseDec"

raiseType :: Type -> ExpQ
raiseType (AppT typ typ2) = [| AppT $(raiseType typ) $(raiseType typ2) |]
raiseType (SigT typ kind) = [| SigT $(raiseType typ) $(raiseType kind) |] -- Type and Kind are the same
raiseType (VarT name) = [| VarT name |]
raiseType (ConT name) = [| ConT name |]
raiseType (PromotedT name) = [| PromotedT name |]
raiseType (TupleT int) = [| TupleT int |]
raiseType (UnboxedTupleT int) = [| UnboxedTupleT int |]
raiseType ArrowT = [| ArrowT |]
raiseType ListT = [| ListT |]
raiseType (PromotedTupleT int) = [| PromotedTupleT int |]
raiseType PromotedNilT = [| PromotedNilT |]
raiseType PromotedConsT = [| PromotedConsT |]
raiseType StarT = [| StarT |]
raiseType ConstraintT = [| ConstraintT |]
raiseType (LitT tylit) = [| LitT tylit |]
