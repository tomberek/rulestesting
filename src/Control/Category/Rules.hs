{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
module Control.Category.Rules where
import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Utilities

import Control.Arrow
import Control.Category.Associative
import Control.Category.Structural
import Control.Category
import Prelude hiding (id,(.))
import qualified Data.Constraint as C
import Control.Arrow.CCA.Free
--import Control.Arrow.TH (ASyn)



category_ruleset :: [Exp -> Q (Maybe Exp)]
category_ruleset = let a = C.Dict :: C.Dict (Arrow (ASyn m))
                       demote = unTypeRule a
                  in [demote category_id_arr,demote category_id,demote category_leftAssoc]