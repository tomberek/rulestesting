-- Miscellaneous utilities on ordinary Haskell syntax used by the arrow
-- translator.

module Language.Haskell.TH.Utilities(
    FreeVars(freeVars), DefinedVars(definedVars),
    failureFree, irrPat, paren, parenInfixArg,
    tuple, tupleP,
    times,
    hsQuote, hsSplice, quoteArr, quoteInit     -- for CCA
) where

import           Data.Generics                (everywhere, mkT)
import           Data.Set                     (Set)
import qualified Data.Set                     as Set
import           Language.Haskell.Exts.Syntax

-- The set of free variables in some construct.

class FreeVars a where
    freeVars :: a -> Set Name

instance FreeVars a => FreeVars [a] where
    freeVars = Set.unions . map freeVars

instance FreeVars Pat where
    freeVars (PVar n) = Set.singleton n
    freeVars (PLit _) = Set.empty
    freeVars (PNeg p) = freeVars p
    freeVars (PInfixApp p1 _ p2) = freeVars p1 `Set.union` freeVars p2
    freeVars (PApp _ ps) = freeVars ps
    freeVars (PTuple _ ps) = freeVars ps
    freeVars (PList ps) = freeVars ps
    freeVars (PParen p) = freeVars p
    freeVars (PRec _ pfs) = freeVars pfs
    freeVars (PAsPat n p) = Set.insert n (freeVars p)
    freeVars (PWildCard) = Set.empty
    freeVars (PIrrPat p) = freeVars p

instance FreeVars PatField where
    freeVars (PFieldPat _ p) = freeVars p

instance FreeVars FieldUpdate where
    freeVars (FieldUpdate _ e) = freeVars e

instance FreeVars Exp where
    freeVars (Var n) = freeVars n
    freeVars (Con _) = Set.empty
    freeVars (Lit _) = Set.empty
    freeVars (InfixApp e1 op e2) =
          freeVars e1 `Set.union` freeVars op `Set.union` freeVars e2
    freeVars (App f e) = freeVars f `Set.union` freeVars e
    freeVars (NegApp e) = freeVars e
    freeVars (Lambda _ ps e) = freeVars e `Set.difference` freeVars ps
    freeVars (Let decls e) =
          (freeVars decls `Set.union` freeVars e) `Set.difference`
                definedVars decls
    freeVars (If e1 e2 e3) =
          freeVars e1 `Set.union` freeVars e2 `Set.union` freeVars e3
    freeVars (Case e as) = freeVars e `Set.union` freeVars as
    freeVars (Do ss) = freeVarsStmts ss
    freeVars (Tuple _ es) = freeVars es
    freeVars (List es) = freeVars es
    freeVars (Paren e) = freeVars e
    freeVars (LeftSection e op) = freeVars e `Set.union` freeVars op
    freeVars (RightSection op e) = freeVars op `Set.union` freeVars e
    freeVars (RecConstr _ us) = freeVars us
    freeVars (RecUpdate e us) = freeVars e `Set.union` freeVars us
    freeVars (EnumFrom e) = freeVars e
    freeVars (EnumFromTo e1 e2) = freeVars e1 `Set.union` freeVars e2
    freeVars (EnumFromThen e1 e2) = freeVars e1 `Set.union` freeVars e2
    freeVars (EnumFromThenTo e1 e2 e3) =
          freeVars e1 `Set.union` freeVars e2 `Set.union` freeVars e3
    -- freeVars (ListComp e ss) = freeVars e `Set.union` freeVarsStmts ss
    freeVars (ExpTypeSig _ e _) = freeVars e

instance FreeVars QOp where
    freeVars (QVarOp n) = freeVars n
    freeVars (QConOp _) = Set.empty

instance FreeVars QName where
    freeVars (UnQual v) = Set.singleton v
    freeVars _ = Set.empty

instance FreeVars Alt where
    freeVars (Alt _ p gas decls) =
          (freeVars gas `Set.union` freeVars decls) `Set.difference`
          (freeVars p `Set.union` definedVars decls)

instance FreeVars GuardedAlts where
    freeVars (UnGuardedAlt e) = freeVars e
    freeVars (GuardedAlts alts) = freeVars alts

instance FreeVars GuardedAlt where
    freeVars (GuardedAlt _ e1 e2) = freeVars e1 `Set.union` freeVars e2

instance FreeVars Decl where
    freeVars (FunBind ms) = freeVars ms
    freeVars (PatBind _ p _ rhs decls) =
          (freeVars rhs `Set.union` freeVars decls) `Set.difference`
          (freeVars p `Set.union` definedVars decls)
    freeVars _ = Set.empty

instance FreeVars Match where
    freeVars (Match _ n ps _ rhs decls) =
          (freeVars rhs `Set.union` freeVars decls) `Set.difference`
          (Set.insert n (freeVars ps) `Set.union` definedVars decls)

instance FreeVars Rhs where
    freeVars (UnGuardedRhs e) = freeVars e
    freeVars (GuardedRhss grs) = freeVars grs

instance FreeVars GuardedRhs where
    freeVars (GuardedRhs _ e1 e2) = freeVars e1 `Set.union` freeVars e2

instance FreeVars Stmt where
    freeVars (Generator _ p e) = freeVars e `Set.difference` freeVars p
    freeVars (Qualifier e) = freeVars e
    freeVars (LetStmt bs) = freeVars bs
    freeVars (RecStmt bs) = freeVars bs

instance FreeVars Binds where
    freeVars (BDecls bs) = freeVars bs
    freeVars (IPBinds bs) = freeVars bs
instance FreeVars IPBind where
    freeVars (IPBind _ i e) = error "freeVars IPBind not defined"

freeVarsStmts :: [Stmt] -> Set Name
freeVarsStmts = foldr addStmt Set.empty
    where addStmt (Generator _ p e) s = freeVars e `Set.union` (s `Set.difference` freeVars p)
          addStmt (Qualifier e) _s = freeVars e
          addStmt (LetStmt decls) s =
                (freeVars decls `Set.union` s) `Set.difference` definedVars decls

-- The set of variables defined by a construct.

class DefinedVars a where
    definedVars :: a -> Set Name

instance DefinedVars a => DefinedVars [a] where
    definedVars = Set.unions . map definedVars

instance DefinedVars Decl where
    definedVars (FunBind (Match _ n _ _ _ _:_)) = Set.singleton n
    definedVars (PatBind _ p _ _ _) = freeVars p
    definedVars _ = Set.empty

instance DefinedVars Binds where
    definedVars (BDecls ds) = definedVars ds
    definedVars (IPBinds ds) = error "definedVars IPBinds not defined"

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
hsQuote e = App (App lq e) rq
  where lq = var "[|"
        rq = var "|]"
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
var = Var . UnQual . Ident