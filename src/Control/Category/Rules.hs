{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
module Control.Category.Rules where
import Control.Arrow.CCA
import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Utilities

import Control.Arrow
import Control.Category.Associative
import Control.Category.Structural
import Control.Category
import Prelude hiding (id,(.))
import qualified Data.Constraint as C
import Control.Arrow.CCA.Optimize

category_id_arr :: RuleT Category a b b
category_id_arr [rule2| arr (\n -> m) |] | m_ == n_ = [|| id ||]
category_id_arr a = return a

category_id_arr' = unTypeRule (C.Dict :: C.Dict (Arrow (ASyn m))) category_id_arr

--category_id :: RuleT Category a b c
category_id [rule2| f >>> id |] = [|| $$f ||]
category_id [rule2| id >>> f |] = [|| $$f ||]
category_id [rule2| f >>> (g >>> h) |] = [|| ($$f >>> $$g) >>> $$h ||]
category_id [rule2| arr (\n -> m) |] | m_ == n_ = [|| id ||]
category_id a = return a
category_id' = unTypeRule (C.Dict :: C.Dict (Arrow (ASyn m))) category_id

category_leftAssoc :: RuleT Category a b c
category_leftAssoc [rule2| f >>> (g >>> h) |] = [|| ($$f >>> $$g) >>> $$h ||]
category_leftAssoc a = return a

category_ruleset :: [Exp -> Q Exp]
category_ruleset = let a = C.Dict :: C.Dict (Arrow (ASyn m))
                       demote = unTypeRule a
                  in [demote category_id_arr,demote category_id,demote category_leftAssoc]