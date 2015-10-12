{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
module Control.Arrow.TH.Structural (fixTuple,buildArr) where
import     Language.Haskell.Exts
import Language.Haskell.Meta
import Language.Haskell.TH.Utilities
import Control.Applicative
import Control.Category.Structural
import Control.Arrow.CCA
import           Control.Category
import           Prelude             hiding (id, (.),fst,snd)
import           Control.Arrow hiding (first,second,(***),(&&&))
import Language.Haskell.TH (mkName)
import qualified Language.Haskell.TH as TH
import Language.Haskell.TH.Lib

pattern P a = PVar a
pattern E a = Var a
pattern EP a rest = Tuple Boxed [a,rest]

fixTuple :: [ExpQ] -> Pat -> Exp -> ExpQ
fixTuple [] pat expr = buildArr pat expr
fixTuple es (PApp a [rest]) (App (Con b) rest2) | toName a == toName b = fixTuple es rest rest2 -- removes application of constructor
fixTuple es PWildCard expr = [| ( $(foldl1 (&:&) es) ) >>> arr (\_ -> $(return $ toExp expr)) |]
fixTuple es pat@(P _) (EP b rest) = [| $(fixTuple es pat b) &&& $(fixTuple es pat rest) |]  -- diag
fixTuple es (P a) (E b) | toName a == toName b                 = [| ($(foldl1 (&:&) $ fmap TH.ParensE <$> es)) |]                                                                  -- id
                        | otherwise                            = [| ($(foldl1 (&:&) $ fmap TH.ParensE <$> es)) >>> $(buildArr (P a) (E b)) |]  -- arr
fixTuple es pat b                                              = do
    [|  $(foldl1 (&:&) (fmap TH.ParensE <$> es)) >>> $(buildArr pat b) |]

buildArr :: Pat -> Exp -> ExpQ
buildArr PWildCard e= [| terminate $(return $ toExp e) |]
buildArr p e | not $ any (flip elem $ freeVars p) (freeVars e)= [| terminate $(return $ toExp e) |]
             | otherwise = [| ( (arr (\ $(return $ toPat p) ->
                 $(promote <$> intermediate p))
                 >>> arr (\ $(intermediate  p) -> $(promote <$> intermediate e))
             >>> arr (\ $(intermediate e) -> $(return $ toExp e)) ) )|] -- >>= return . error .show
             where
                 intermediate vars = return $ tuplizer (TH.TupP []) TH.TupP <$> map (TH.VarP . toName) $ freeVars vars

(&:&) :: ExpQ -> ExpQ -> ExpQ
expr1 &:& expr2 = infixE (Just expr1) (varE $ mkName "&&&") (Just expr2)
