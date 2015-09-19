{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
module Control.Categorical.Bifunctor.Rules where

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
import Unsafe.Coerce
import Data.Proxy
--import Control.Arrow.TH (ASyn)

{-
bifunctor_ruleset :: [Exp -> Q (Maybe Exp)]
bifunctor_ruleset = let a = C.Dict :: C.Dict (Arrow (ASyn m))
               demote = unTypeRule a
          in [demote category_id_arr,demote category_id,demote category_leftAssoc]

                                                        , ([| \(a,b) -> (a,b)|],Id)
                                                        , ([| \(a,(b,c)) -> (a,(b,c))|],Id)
                                                        , ([| \((a,b),c) -> ((a,b),c)|],Id) -- so far only two levels
                                                        , ([| \a -> () |],Terminate $ TupE [])
                                                        -}
category_id_arr :: RuleT (Category a) (a b b)
category_id_arr [rule2| arr (\n -> m) |] | m_ == n_ = into [|| id ||]
category_id_arr [rule2| \n -> m |] | m_ == n_ = into [|| id ||]
category_id_arr [rule2| arr id |] = into [|| id ||]
category_id_arr [rule2| returnA |] = into [|| id ||]
category_id_arr a = return Nothing

category_id_arr' = unTypeRule (C.Dict::C.Dict (Category (->))) category_id_arr


category_id :: RuleT (Category a) (a b c)
category_id [rule2| f >>> id |] = into [|| $$f ||]
category_id [rule2| id >>> f |] = into [|| $$f ||]
category_id [rule2| f >>> (g >>> h) |] = into [|| ($$f >>> $$g) >>> $$h ||]
category_id a = return Nothing

category_leftAssoc :: RuleT (Category a) (a b c)
category_leftAssoc [rule2| f >>> (g >>> h) |] = into [|| ($$f >>> $$g) >>> $$h ||]
category_leftAssoc a = return Nothing