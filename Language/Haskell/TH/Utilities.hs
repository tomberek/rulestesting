{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE LambdaCase #-}
-- Miscellaneous utilities on ordinary Haskell syntax used by the arrow
-- translator.

module Language.Haskell.TH.Utilities(
    FreeVars(freeVars), DefinedVars(definedVars),
    failureFree, irrPat, paren, parenInfixArg,
    tuple, tupleP, tuplizer,
    times,
    hsQuote, hsSplice, quoteArr, quoteInit,     -- for CCA
    rule,promote,promote',ifM,areExpAEq,expEqual --for id detection
) where

import           Data.Generics                (everywhere, mkT)
import           Data.List
import           Language.Haskell.Exts.Syntax
import qualified Language.Haskell.TH as TH
import qualified Language.Haskell.TH.Quote as TH
import qualified Language.Haskell.TH.Syntax as TH
import           Language.Haskell.TH.Alpha
import Language.Haskell.Meta
import Control.Applicative

{-
tuplize :: [Pat] -> Pat
tuplize [] = PWildCard
tuplize [s] =s
tuplize (s:ss) = PTuple Boxed [s, tuplize ss]
-}

tuplizer :: a -> ([a]->a) -> [a] -> a
tuplizer u _ [] = u
tuplizer _ _ [a] = a
tuplizer u f (a:as) = f [a,tuplizer u f as]

-- | Like @if@, but where the test can be monadic.
ifM :: Monad m => m Bool -> m a -> m a -> m a
ifM b t f = do b' <- b; if b' then t else f

promote :: TH.Pat -> TH.Exp
promote (TH.ConP _ [pat]) = promote pat
promote (TH.ConP _ pats) = TH.TupE $ map promote pats
--promote (TH.VarP (Name s@['_',_,'_']))) = TH.VarE _
promote (TH.VarP n) = TH.VarE n
promote (TH.LitP n) = TH.LitE n
promote (TH.TupP pats) = TH.TupE $ map promote pats
promote (TH.ParensP pat) = TH.ParensE $ promote pat
promote (TH.ListP pats) = TH.ListE $ map promote pats
promote (TH.WildP) = TH.TupE []
promote x = error $ "pattern promotion TODO" ++ show x

-- | Does not support qualified names or other module matching, only NameS dynamically matched names
promoteName :: TH.Name -> TH.PatQ
promoteName (Name s) = [p| TH.Name (TH.OccName $(TH.litP $ TH.stringL s)) |] >>= return .
                    \case TH.ConP a b -> TH.ConP a (b ++ [TH.WildP])
                         -- NOTE: Is there a better way to do this? TH.WildP and $TH.WildP does not work

-- | Of single Var
promotePat :: TH.Pat -> TH.PatQ
promotePat (TH.TupP ps) = [p| TH.TupP $(TH.ListP <$> mapM promotePat ps) |] -- >>= return . error . show
promotePat (TH.VarP (Name s@['_',t,'_'])) =
    [p| (promote -> $( [p| (TH.returnQ -> $(TH.varP $ Name s)) |]
        >>= return . TH.AsP (Name $ "_" ++ s ++ "_"))) |]
    >>= return. TH.AsP (Name $ "_'" ++ [t] ++ "_")

promote' :: TH.Exp -> TH.PatQ
promote' (TH.VarE (Name s@['_',_,'_'])) = [p| (TH.returnQ -> $(TH.varP $ Name s)) |] >>= return . TH.AsP (Name ("_" ++ s ++ "_"))
promote' (TH.VarE n) = [p| TH.VarE $(promoteName n) |]
promote' (TH.AppE n e) = [p| TH.AppE $(promote' n) $(promote' e) |]
promote' (TH.TupE es) = [p| TH.TupE $(TH.ListP <$> mapM promote' es) |]
promote' (TH.InfixE (Just e1) o (Just e2)) = [p| TH.UInfixE $(promote' e1) $(promote' o) $(promote' e2) |]
promote' (TH.UInfixE e1 o e2) = [p| TH.InfixE (Just $(promote' e1)) $(promote' o) (Just $(promote' e2)) |]
promote' (TH.ParensE e) = promote' e -- parseExp produces an extra parens on a lambda
--promote' (TH.ParensE e) = [p| TH.ParensE $(promote' e) |]
promote' (TH.LamE ps e) = [p| TH.LamE $(TH.ListP <$> mapM promotePat ps) $(promote' e)|] -- >>= return . error . show
promote' a = error $ "promote' error: " ++ show a

pattern Name s = (TH.Name (TH.OccName s) TH.NameS)

rule :: TH.QuasiQuoter
rule = TH.QuasiQuoter {
        TH.quoteExp = \input -> case parseExp input of
            Right b -> [| promote' b |]
            Left c -> error $ "Exp: cannot parse rule pattern: " ++ c ++ " " ++ input
      , TH.quotePat = \input -> case parseExp input of
             Right b -> promote' b
             Left c -> error $ "cannot parse rule pattern: " ++ c ++ " " ++ input
      , TH.quoteDec = error "cannot be declarations."
      , TH.quoteType = error "cannot be types."
        }

-- The set of free variables in some construct.
class FreeVars a where
    freeVars :: a -> [Name]

instance FreeVars a => FreeVars [a] where
    freeVars = foldl' union [] . map freeVars

instance FreeVars Pat where
    freeVars (PVar n) = [n]
#if __GLASGOW_HASKELL__ <= 708
    freeVars (PLit _) = []
    freeVars (PNeg p) = freeVars p
#else
    freeVars (PLit _ _) = []
#endif
    freeVars (PInfixApp p1 _ p2) = freeVars p1 `union` freeVars p2
    freeVars (PApp _ ps) = freeVars ps
    freeVars (PTuple _ ps) = freeVars ps
    freeVars (PList ps) = freeVars ps
    freeVars (PParen p) = freeVars p
    freeVars (PRec _ pfs) = freeVars pfs
    freeVars (PAsPat n p) = n : (freeVars p)
    freeVars (PWildCard) = []
    freeVars (PIrrPat p) = freeVars p
    freeVars _ = error "freeVars for Pat not fully implemented"

instance FreeVars PatField where
    freeVars (PFieldPat _ p) = freeVars p
    freeVars _ = error "freeVars for PatField not fully implemented"

instance FreeVars FieldUpdate where
    freeVars (FieldUpdate _ e) = freeVars e
    freeVars _ = error "freeVars for FieldUpdate not fully implemented"

instance FreeVars Exp where
    freeVars (Var n) = freeVars n
    freeVars (Con _) = []
    freeVars (Lit _) = []
    freeVars (InfixApp e1 op e2) =
          freeVars e1 `union` freeVars op `union` freeVars e2
    freeVars (App f e) = freeVars f `union` freeVars e
    freeVars (NegApp e) = freeVars e
    freeVars (Lambda _ ps e) = freeVars e \\ freeVars ps
    freeVars (Let decls e) =
          (freeVars decls `union` freeVars e) \\ definedVars decls
    freeVars (If e1 e2 e3) =
          freeVars e1 `union` freeVars e2 `union` freeVars e3
    freeVars (Case e as) = freeVars e `union` freeVars as
    freeVars (Do ss) = freeVarsStmts ss
    freeVars (Tuple _ es) = freeVars es
    freeVars (List es) = freeVars es
    freeVars (Paren e) = freeVars e
    freeVars (LeftSection e op) = freeVars e `union` freeVars op
    freeVars (RightSection op e) = freeVars op `union` freeVars e
    freeVars (RecConstr _ us) = freeVars us
    freeVars (RecUpdate e us) = freeVars e `union` freeVars us
    freeVars (EnumFrom e) = freeVars e
    freeVars (EnumFromTo e1 e2) = freeVars e1 `union` freeVars e2
    freeVars (EnumFromThen e1 e2) = freeVars e1 `union` freeVars e2
    freeVars (EnumFromThenTo e1 e2 e3) =
          freeVars e1 `union` freeVars e2 `union` freeVars e3
    -- freeVars (ListComp e ss) = freeVars e `union` freeVarsStmts ss
    freeVars (ExpTypeSig _ e _) = freeVars e
    freeVars (LeftArrApp _ p) = freeVars p
    freeVars _ = error "freeVars for Exp not fully implemented"

instance FreeVars QOp where
    freeVars (QVarOp n) = freeVars n
    freeVars (QConOp _) = []

instance FreeVars QName where
    freeVars (UnQual v@(Ident _)) = [v]
    freeVars _ = []

#if __GLASGOW_HASKELL__ <= 708
instance FreeVars Alt where
    freeVars (Alt _ p gas decls) =
          (freeVars gas `union` freeVars decls) \\ (freeVars p `union` definedVars decls)

instance FreeVars GuardedAlts where
    freeVars (UnGuardedAlt e) = freeVars e
    freeVars (GuardedAlts alts) = freeVars alts

instance FreeVars GuardedAlt where
    freeVars (GuardedAlt _ e1 e2) = freeVars e1 `union` freeVars e2
#else
instance FreeVars Alt where
    freeVars (Alt _ p rhs binds) =
          (freeVars rhs `union` freeVars binds) \\ (freeVars p `union` definedVars binds)
#endif

instance FreeVars Decl where
    freeVars (FunBind ms) = freeVars ms
#if __GLASGOW_HASKELL__ <= 708
    freeVars (PatBind _ p _ rhs decls) =
#else
    freeVars (PatBind _ p rhs decls) =
#endif
          (freeVars rhs `union` freeVars decls) \\ (freeVars p `union` definedVars decls)
    freeVars _ = []

instance FreeVars Match where
    freeVars (Match _ n ps _ rhs decls) =
          (freeVars rhs `union` freeVars decls) \\ (n : ((freeVars ps) `union` definedVars decls))

instance FreeVars Rhs where
    freeVars (UnGuardedRhs e) = freeVars e
    freeVars (GuardedRhss grs) = freeVars grs

instance FreeVars GuardedRhs where
    freeVars (GuardedRhs _ e1 e2) = freeVars e1 `union` freeVars e2

instance FreeVars Stmt where
    freeVars (Generator _ p e) = freeVars e -- changed
    freeVars (Qualifier e) = freeVars e
    freeVars (LetStmt bs) = freeVars bs
    freeVars (RecStmt bs) = freeVars bs

instance FreeVars Binds where
    freeVars (BDecls bs) = freeVars bs
    freeVars (IPBinds bs) = freeVars bs
instance FreeVars IPBind where
    freeVars (IPBind _ _ _) = error "freeVars IPBind not defined"

freeVarsStmts :: [Stmt] -> [Name]
freeVarsStmts = foldr addStmt []
    where addStmt (Generator _ p e) s = freeVars e `union` (s \\ freeVars p)
          addStmt (Qualifier e) _ = freeVars e
          addStmt (LetStmt decls) s =
                (freeVars decls `union` s) \\ definedVars decls
          addStmt _ _ = error "Only Generator,Qualifier and LetStmt implemented in freeVarsStmts"

-- The set of variables defined by a construct.

class DefinedVars a where
    definedVars :: a -> [Name]

instance DefinedVars a => DefinedVars [a] where
    definedVars = foldl' union [] . map definedVars

instance DefinedVars Decl where
    definedVars (FunBind (Match _ n _ _ _ _:_)) = [n]
#if __GLASGOW_HASKELL__ <= 708
    definedVars (PatBind _ p _ _ _) = freeVars p
#else
    definedVars (PatBind _ p _ _) = freeVars p
#endif
    definedVars _ = []

instance DefinedVars Binds where
    definedVars (BDecls ds) = definedVars ds
    definedVars (IPBinds _) = error "definedVars IPBinds not defined"

-- Is the pattern failure-free?
-- (This is incomplete at the moment, because patterns made with unique
-- constructors should be failure-free, but we have no way of detecting them.)
failureFree :: Pat -> Bool
failureFree (PVar _) = True
failureFree (PApp n ps) = n == unit_con_name && null ps
failureFree (PTuple _ ps) = all failureFree ps
failureFree (PParen p) = failureFree p
failureFree (PAsPat _ p) = failureFree p
failureFree (PWildCard) = True
failureFree (PIrrPat _) = True
failureFree _ = False

-- Irrefutable version of a pattern

irrPat :: Pat -> Pat
irrPat p@(PVar _) = p
irrPat (PParen p) = PParen (irrPat p)
irrPat (PAsPat n p) = PAsPat n (irrPat p)
irrPat p@(PWildCard) = p
irrPat p@(PIrrPat _) = p
irrPat p = PIrrPat p

-- Make an expression into an aexp, by adding parentheses if required.

paren :: Exp -> Exp
paren e = if isAexp e then e else Paren e
    where isAexp (Var _) = True
          isAexp (Con _) = True
          isAexp (Lit _) = True
          isAexp (Paren _) = True
          isAexp (Tuple _ _) = True
          isAexp (List _) = True
          isAexp (EnumFrom _) = True
          isAexp (EnumFromTo _ _) = True
          isAexp (EnumFromThen _ _) = True
          isAexp (EnumFromThenTo _ _ _) = True
          isAexp (ListComp _ _) = True
          isAexp (LeftSection _ _) = True
          isAexp (RightSection _ _) = True
          isAexp (RecConstr _ _) = True
          isAexp (RecUpdate _ _) = True
          isAexp _ = False

-- Make an expression into an fexp, by adding parentheses if required.

parenInfixArg :: Exp -> Exp
parenInfixArg e@(App _ _) = e
parenInfixArg e = paren e

-- Tuples

tuple :: [Exp] -> Exp
tuple [] = unit_con
tuple [e] = e
tuple es = Tuple Boxed es

tupleP :: [Pat] -> Pat
tupleP [] = PApp unit_con_name []
tupleP [e] = e
tupleP es = PTuple Boxed es

-- Compose a function n times.

times :: Int -> (a -> a) -> a -> a
times n f a = foldr ($) a (replicate n f)

-- | helper for template haskell syntax hack
hsQuote :: Exp -> Exp
hsQuote e = App (App lq e) rq
  where lq = var "[|"
        rq = var "|]"
hsSplice :: Exp -> Exp
hsSplice e = App (App lq e) rq
  where lq = var "$("
        rq = var ")"
quoteArr :: Exp -> Exp
-- quoteArr f = hsSplice (App (var "arr") (hsQuote f))
quoteArr f = App (App (var "arr'") (hsQuote f)) f
quoteInit :: Exp -> Exp
quoteInit = everywhere (mkT aux)
  where
     aux (App (Var (UnQual (Ident "init"))) i) = App (App (var "init'") (hsQuote i)) i
     aux x = x
var :: String -> Exp
var = Var . UnQual . Ident
