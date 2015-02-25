{-# LANGUAGE GADTs #-}
{-# LANGUAGE Arrows #-}
-- | Main entry point to the application.
module Main where

import Control.Arrow
import Control.Category
import Prelude hiding (id,(.))
import Debug.Trace

{-# RULES
"arr>>>2"   forall f g h. (Arr f) >:> ( (Arr g) >:> h) = trace "fired2" ( (Arr (g . f)) >:> h)
"arr>>"     forall f g. (Arr f) >:> (Arr g) = trace "fired1" $ Arr (g . f)
 #-}

data Arr a b where
    Arr :: (a -> b) -> Arr a b
    First :: Arr a b -> Arr (a, d) (b, d)
    Second :: Arr a b -> Arr (d, a) (d, b)
    Effect :: f a b -> Arr a b
    (:***) :: Arr a b -> Arr c d -> Arr (a,c) (b,d)
    Next :: Arr a c -> Arr c b -> Arr a b
    Loop :: Arr (a, d) (b, d) -> Arr a b
    LoopD :: e -> ((a, e) -> (b, e)) -> Arr a b
    Init :: b -> Arr b b
    Fan :: Arr a b -> Arr a c -> Arr a (b,c)

{-# NOINLINE (>:>) #-}
(>:>) :: Arr a c -> Arr c b -> Arr a b
f >:> g = Next f g

instance Show (Arr a b) where
    show (Arr _) = "Arr"
    show (First f) = "First " ++ show f
    show (Second f) = "Second " ++ show f
    show (Effect _) = "Effect"
    show (Next f g) = "(" ++ show f ++ " . " ++ show g ++ ")"
    show (f :*** g) = "[" ++ show f ++ " *** " ++ show g ++ "]"
    show (Loop f) = "Loop " ++ show f
    show (LoopD _ _) = "LoopD"
    show (Init _) = "Init"
    show (Fan f g) = "<" ++ show f ++ " &&& " ++ show g ++ ">"

instance Category (Arr ) where
  id = Arr id
  (.) = flip (>:>)

instance Arrow (Arr ) where
    arr = Arr
    first = First
    second = Second
    (***) = (:***)
    (&&&) = Fan
instance ArrowLoop (Arr ) where
    loop = Loop
instance ArrowInit (Arr ) where
    init = Init
class ArrowLoop a => ArrowInit a where
    init :: b -> a b b

arrow :: Arr (Int,Int) Int
arrow = proc (x,y) -> do
    a <- arr (+1) -< x
    b <- arr (+1) -< y
    returnA -< (a+b)

main :: IO ()
main = do
    print arrow