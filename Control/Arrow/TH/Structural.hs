{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
module Control.Arrow.TH.Structural (fixTuple) where
import     Language.Haskell.Exts
import Language.Haskell.Meta
import Language.Haskell.TH.Utilities
import Language.Haskell.TH (ExpQ)
import Control.Applicative
import Control.Category.Associative
import Control.Category.Structural
import Control.Category.Monoidal
import Control.Category.Cartesian
import Control.Categorical.Bifunctor
import Control.Arrow.CCA
import           Control.Category
import           Prelude             hiding (id, (.),fst,snd)
import           Control.Arrow hiding (first,second,(***),(&&&))
import Language.Haskell.TH (reportWarning,mkName)
import qualified Language.Haskell.TH as TH
import Language.Haskell.TH.Lib

pattern P a = PVar a
pattern E a = Var a
pattern TP a rest = PTuple Boxed [a,rest]
pattern EP a rest = Tuple Boxed [a,rest]

fixTuple :: [ExpQ] -> Pat -> Pat -> Exp -> (Pat,ExpQ)
--fixTuple [] origp pat exp = (origp,[| arr (\ $(return $ toPat pat) -> $(return $ toExp exp)) |])
fixTuple es origp pat@(PApp a [rest]) (App (Con b) rest2) | toName a == toName b = fixTuple es origp rest rest2 -- removes application of constructor
fixTuple es origp PWildCard exp = (origp,[| ( $(foldl1 (&:&) es) ) >>> arr (\_ -> $(return $ toExp exp)) |])
fixTuple es origp pat@(P a) (EP b rest) = (origp, [| $(fixTuple es origp pat b) &&& $(fixTuple es origp pat rest) |] )  -- diag
                            {-
fixTuple es (P a) (E b) | toName a == toName b                 = [| ($(foldl1 (&:&) es)) >>> id|]                                                                  -- id
                        | otherwise                            = [| ($(foldl1 (&:&) es)) >>> arr (\ $(return $ toPat $ P a) -> $(return $ toExp $ E b)) |]  -- arr
fixTuple [e1,e2] pat@(TP a rest@(fmap toName . freeVars -> restFree)) (EP b rest2@(fmap toName . freeVars -> rest2Free))        -- ***
                  |  all (flip elem (toName <$> freeVars a)) (toName <$> freeVars b)
                      && (all (flip elem restFree) rest2Free)       = do
                          reportWarning $ "success: " ++ show rest
                          [| $(fixTuple [e1] a b) *** $(fixTuple [e2] rest rest2) |]                        -- ***
                  | otherwise                                       = do
                          reportWarning $ "failed: " ++ show rest
                          [| $(fixTuple [e2] a b) *** $(fixTuple [e1] rest rest2) |]                        -- ***
fixTuple [e1,e2] pat@(TP a rest) b
                  | all ( flip elem (toName <$> freeVars a)) (toName <$> freeVars b) = do
                      reportWarning $ "weakeneing: " ++ show pat
                      [| $(fixTuple [e1] a b) |]                           -- fst
                  | all ( flip elem (toName <$> freeVars rest)) (toName <$> freeVars b) = do
                      reportWarning $ "weakeneing: " ++ show pat
                      [| $(fixTuple [e2] rest b) |]                           -- snd (or something)
                  | otherwise                                       = do
                      reportWarning $ "cant fix for vars: " ++ (show $ (pat,freeVars b))
                      [| $(foldl1 (&:&) [e1,e2] ) >>> arr (\ $(return $ toPat pat) -> $(return $ toExp b)) |] -- can't "categorize"
                        -}
fixTuple es origp pat b                                              = (origp,do
    --reportWarning $ "var: " ++ (show (freeVars pat,freeVars b,show es,show origp))
    --reportWarning $ "exps: " ++ (show $ (pat,b))
    [|  $(foldl1 (&:&) (fmap TH.ParensE <$> es)) >>> arr (\ $(return $ toPat pat) -> $(return $ toExp b))  |]) -- can't "categorize"

(&:&) :: ExpQ -> ExpQ -> ExpQ
expr1 &:& expr2 = infixE (Just expr1) (varE $ mkName "&&&") (Just expr2)
(*:*) :: ExpQ -> ExpQ -> ExpQ
expr1 *:* expr2 = infixE (Just expr1) (varE $ mkName "***") (Just expr2)