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

pattern P a = PVar a
pattern E a = Var a
pattern TP a rest = PTuple Boxed [a,rest]
pattern EP a rest = Tuple Boxed [a,rest]

fixTuple :: Pat -> Exp -> ExpQ
--fixTuple pat@(PApp a [rest]) (App (Con b) rest2) | toName a == toName b = fixTuple rest rest2
fixTuple PWildCard exp = [| arr (\_ -> $(return $ toExp exp)) |]
fixTuple pat@(P a) (EP b rest) = [| $(fixTuple pat b) &&& $(fixTuple pat rest) |]                                                     -- diag
fixTuple (P a) (E b) | toName a == toName b                 = [|id|]                                                                  -- id
                     | otherwise                            = [| arr (\ $(return $ toPat $ PWildCard) -> $(return $ toExp $ E b)) |]  -- arr
                     {-
fixTuple pat@(TP a rest@(fmap toName . freeVars -> restFree)) (EP b rest2@(fmap toName . freeVars -> rest2Free))
          |  all (flip elem (toName <$> freeVars a)) (toName <$> freeVars b)
              && (all (flip elem restFree) rest2Free)       = [| $(fixTuple a b) *** $(fixTuple rest rest2) |]                        -- ***
          | otherwise                                       = [| swap >>> $(fixTuple (TP rest a) (EP b rest2)) |]      -- swap
fixTuple pat@(TP a rest) (E b)
          | elem (toName b) (toName <$> freeVars a)         = [| fst >>> $(fixTuple a (E b)) |]                           -- fst
          | otherwise                                       = [| swap >>> $(fixTuple (TP rest a) (E b)) |]             -- swap
                     -}
fixTuple pat b                                              = [| arr (\ $(return $ toPat pat) -> $(return $ toExp b)) |] -- can't "categorize"