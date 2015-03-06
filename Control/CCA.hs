{-# LANGUAGE TemplateHaskell, FlexibleInstances #-}
-- originally from CCA package: https://hackage.haskell.org/package/CCA-0.1.5.2

module Control.CCA 
  ((>>>), (<<<), first, second, (***), (&&&), loop, 
   Arrow, ArrowLoop, ArrowInit, 
   arr, init, arr', init', constant,
   norm, normOpt) where

import Control.Arrow hiding (arr, returnA)
import Control.CCA.Types hiding (init)
import Control.CCA.CCNF
import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Instances
import Prelude hiding (init)

arr :: ExpQ -> ExpQ
arr e = appE [|arr' e|] e

init :: ExpQ -> ExpQ

init i = appE [|init' i|] i

instance Lift a => Lift (Q a) where
  lift x = x >>= \x -> [| return x |]
constant :: (ArrowInit a, Lift b) => b -> a () b
constant c = arr' [|const c|] (const c)

