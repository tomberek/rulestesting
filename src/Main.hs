{-# LANGUAGE GADTs #-}
{-# LANGUAGE Arrows #-}
-- | Main entry point to the application.
module Main where

import Control.Arrow
import Control.Category
import Prelude hiding (id,(.))
import Debug.Trace

{-

"arr>>>2"   forall f g h. (Arr f) >:> ( (Arr g) >:> h) = trace "fired2" ( (Arr (g . f)) >:> h)
"arr>>"     forall f g. (Arr f) >:> (Arr g) = trace "fired1" $ Arr (g . f)
"larger"    forall x2 y2
                       (x::forall a b. (a,b)-> a         )
                       (f::forall a b. (a,b)->((a,()),b) )
                       (s::forall a b. (a,b)-> (b,a)     ).
                       (( Arr f >:> First (Arr x >:> x2)) >:> Arr s ) >:>
                       (( Arr f >:> First (Arr x >:> y2)) >:> Arr s ) = trace "large" $ (:***) x2 y2
"dots"      forall x y z. x >:> (y >:> z) = trace "dots" $ (x >:> y) >:> z
"par"   forall f g. Raise >:> (Fst >:> ((Pierce >:> (First (Fst >:> f) >:> Swap)) >:>
                     ((Pierce >:> (First (Fst >:> g) >:> Swap)) >:> (Raise >:> (Fst >:> Id2))))) = trace "par" (f :*** g)
---}
{-# RULES
"bump"  forall (f::a -> (a,())).       arr2 f = trace "bump" $ Bump
"raise" forall (f::(a,b)->((a,b),())). arr2 f = trace "raise" $ Raise
"pierce"forall (f::(a,b)->((a,()),b)). arr2 f = trace "pierce" $ Pierce
"swap"  forall (f::(a,b)->(b,a)).      arr2 f = trace "swap" $ Swap
"fst"   forall (f::(a,b)->a).          arr2 f = trace "fst" $ Fst
"id"    forall (f::forall a. a->a).    arr2 f = trace "id" $ Id2
"test2" Fst >:> Id2  = trace "test2" $ Fst
"test"  forall f. next Raise (next Fst f) = trace "test" $ f
 #-}

data Arr a b where
    Raise :: Arr (a,b) ((a,b),())
    Pierce :: Arr (a,b) ((a,()),b)
    Fst :: Arr (a,b) a
    Bump :: Arr a (a,())
    Id2 :: Arr a a
    Swap :: Arr (a,b) (b,a)
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

{-# NOINLINE arr2 #-}
arr2 :: (a->b) -> Arr a b
arr2 = Arr
{-# NOINLINE first2 #-}
first2 :: Arr (a,b) ((a,()),b)
first2 = Pierce
{-# NOINLINE bump #-}
bump :: Arr Int (Int,())
bump = Bump

{-# NOINLINE (>:>) #-}
(>:>) :: Arr a c -> Arr c b -> Arr a b
f >:> g = Next f g
{-# NOINLINE next #-}
next :: Arr a c -> Arr c b -> Arr a b
next = (>:>)

instance Show (Arr a b) where
    show (Arr _) = "Arr"
    show (Id2) = "Id2"
    show (Fst) = "Fst"
    show (Raise) = "Raise"
    show (Pierce) = "Pierce"
    show (Bump) = "Bump"
    show (Swap) = "Swap"
    show (First f) = "First " ++ show f
    show (Second f) = "Second " ++ show f
    show (Effect _) = "Effect"
    show (Next f g) = "(" ++ show f ++ " >:> " ++ show g ++ ")"
    show (f :*** g) = "[" ++ show f ++ " *** " ++ show g ++ "]"
    show (Loop f) = "Loop " ++ show f
    show (LoopD _ _) = "LoopD"
    show (Init _) = "Init"
    show (Fan f g) = "<" ++ show f ++ " &&& " ++ show g ++ ">"

instance Category (Arr ) where
  id = arr2 id
  (.) = flip next

instance Arrow (Arr ) where
    arr = arr2
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

arrow :: Arr (Int,Int) (Int,Int)
arrow = proc (x,y) -> do
    a <- arr (+1) -< x
    b <- arr (+2) -< y
    returnA -< (a,b)

main :: IO ()
main = do
    print arrow