{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE Arrows #-}
module Main where

import Control.Arrow hiding (arr)
import qualified Control.Arrow as A
import Control.Category
import Prelude hiding (id,(.))

import Debug.Trace
import Data.List (intercalate)
import Language.Haskell.Meta
import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Examples hiding (arr)
import Parser
import qualified Control.CCA as C
import qualified Control.CCA.CCNF as CCNF
import qualified Control.CCA.Types as Types

{-# RULES
"id"    forall (f::forall a. a->a).    arr2 f = trace "id2" $ Id2
"pierce"forall (f::(a,b)->((a,()),b)). arr2 f = trace "pierce" $ Pierce
"pierc3"forall (f::(a,b)->((a,()),(a,b))). arr2 f = trace "pierc3" $ Pierce3

"rotate"forall (f::(c,(a,b))->(a,b,c) ). arr2 f = trace "rotate" $ Swap3
"swap"  forall (f::(a,b)->(b,a)).      arr2 f = trace "swap" $ Swap

"promote" forall (f::(a,b,c)->((a,()),(b,c))). arr2 f = trace "promote" $ Promote31
"promote" forall (f::(a,b,c)->((b,()),(a,c))). arr2 f = trace "promote" $ Promote32
"promote" forall (f::(a,b,c)->((c,()),(a,b))). arr2 f = trace "promote" $ Promote33

"pier"  forall (f::(a,b)->((a,()),b)). arr2 f = trace "pierce" $ Pierce
"split" forall (f::a->(a,a)).          arr2 f = trace "split" $ error "split"
"walk"  forall (f::(a,b,c)->(b,c,a)).  arr2 f = trace "walk" $ error "walk"
"walk2"  forall (f::(a,b,c)->(b,a,c)).  arr2 f = trace "walk2" $ error "walk2"
"fst"   forall (f::(a,b)->a).          arr2 f = trace "fst" $ Fst
"raise" forall (f::a->(a,())).         arr2 f = trace "raise" $ Raise
"rais2" forall (f::a->((a, () ),() )  ).    arr2 f = trace "rais2" $ error "rais2"
 #-}
{-
---}

data Arr m a b where
    Raise :: Arr m a (a,())
    Pierce :: Arr m (a,b) ((a,()),b)
    Pierce3 :: Arr m (a,b) ((a,()),(a,b))
    Promote31 :: Arr m (a,b,c) ((a,()),(b,c))
    Promote32 :: Arr m (a,b,c) ((b,()),(a,c))
    Promote33 :: Arr m (a,b,c) ((c,()),(a,b))
    Fst :: Arr m (a,b) a
    Id2 :: Arr m a a
    Swap :: Arr m (a,b) (b,a)
    Swap3 :: Arr m (c,(a,b)) (a,b,c)
    Arr :: (a -> b) -> Arr m a b
    First :: Arr m a b -> Arr m (a, d) (b, d)
    Second :: Arr m a b -> Arr m (d, a) (d, b)
    Effect :: m a b -> Arr m a b
    (:***) :: Arr m a b -> Arr m c d -> Arr m (a,c) (b,d)
    (:>>>) :: Arr m a c -> Arr m c b -> Arr m a b
    Loop :: Arr m (a, d) (b, d) -> Arr m a b
    LoopD :: e -> ((a, e) -> (b, e)) -> Arr m a b
    Init :: b -> Arr m b b
    Fan :: Arr m a b -> Arr m a c -> Arr m a (b,c)

{-# NOINLINE arr2 #-}
arr2 :: (a->b) -> Arr m a b
arr2 = Arr

arr3 :: Arr m (Int,Integer) (Int,Integer)
arr3 = proc (x,y) -> do
        a <- arr (+1) -< x
        b <- arr (+2) -< x
        c <- arr (+3) -< y
        id -< (a,c)
arr4 :: Int -> Int
arr4 = proc n -> do
    Just a <- arr (\x->Just $ 1+x) -< n
    id -< a

--g =  [||  [arrow| proc n -> arr (+1) -< n |] :: Int -> Int ||]

arr :: Arrow a => (b->c) -> a b c
arr y= trace "hello" $ A.arr y

runCCNF :: e -> ((b, e) -> (c, e)) -> [b] -> [c]
runCCNF i f = g i
        where g i (x:xs) = let (y, i') = f (x, i)
                            in y : g i' xs

nth' :: Int -> (b, ((), b) -> (a, b)) -> a
nth' n (i, f) = aux n i
  where
    aux n i = x `seq` if n == 0 then x else aux (n-1) i'
      where (x, i') = f ((), i)
runIt x = nth' 0

(a,optimized) = $(CCNF.normOpt f)

out :: Arr m Int Int
out = $(CCNF.norm f)

boring :: Arr m Int Int
boring = f
main :: IO ()
main = do
    --(runQ $ unTypeQ g) >>= print
    print $ optimized 4
    print out
    print boring
    --print $ _
    --print $ f 4
    --print $ e 4
    {-
    runQ [arrow|
        proc n -> do
        Just a <- arr (\x -> Just x) -< n
        let b = a + a
        returnA -< b
            |]
    
    print "done"
    {-
    --}
    --}
    -- draw $ take 2 $ iterate normalize arrow
{--
type Traversal = forall a b m. Arr m a b -> Arr m a b
imap :: Traversal  -> Traversal
imap h (First f) = First (h f)
imap h (f :>>> g) = h f :>>> h g
imap h (Loop f) = Loop (h f)
imap h x = x

norm :: Arr m a b -> Arr m a b
norm (Pierce :>>> (First (Fst :>>> f) :>>> Swap)) = First f :>>> Swap
norm ((Pierce3 :>>> (First (Fst :>>> f) :>>> Swap3)) :>>>
     ((Promote31 :>>> (First (Fst :>>> g) :>>> Swap3)) :>>>
     ((Promote31 :>>> (First (Fst :>>> h) :>>> Swap3)) :>>> i))) = ( (Fan f g) :*** h) :>>> Arr (\((a,b),c) -> (a,b,c)) :>>> i
norm ((First f :>>> Swap) :>>> (First g :>>> Swap)) = f :*** g
norm (Raise :>>> Fst) = Id2
norm (Raise :>>> (Fst :>>> g)) = g
norm (Id2 :>>> g) = g
norm (g :>>> Id2) = g
{-
---}
norm (Arr f :>>> Arr g) = Arr (g . f)           -- original and below
norm (First (Arr f)) = Arr (f `cross` id)
norm (Arr f :>>> LoopD i g) = LoopD i (g . (f `cross` id))
norm (LoopD i f :>>> Arr g) = LoopD i ((g `cross` id) . f)
norm (LoopD i f :>>> LoopD j g) = LoopD (i,j) (assoc' (juggle' (g `cross` id) . (f `cross` id)))
norm (Loop (LoopD i f)) = LoopD i (trace' (juggle' f))
norm (First (LoopD i f)) = LoopD i (juggle' (f `cross` id))
norm (Loop (Arr f)) = Arr (trace' f)
norm (Init i) = LoopD i swap
norm e = e
--normalize ArrowChoice?

everywhere :: Traversal -> Traversal
everywhere h =h. imap (everywhere h)

normalize :: Arr m a b -> Arr m a b
normalize = everywhere norm

swap (x,y) = (y,x)
cross f g (a,b) = (f a,g b)
assoc ((x,y),z) = (x,(y,z))
assoc' f = assoc . f . unassoc
unassoc (x,(y,z)) = ((x,y),z)
juggle ((x,y),z) = ((x,z),y)
juggle' f = juggle . f . juggle
trace' f x = let (y,z) = f (x,z) in y
---}

instance Show (Arr m a b) where
    show (Arr _) = "Arr"
    show (Id2) = "Id2"
    show (Fst) = "Fst"
    show (Raise) = "Raise"
    show (Promote31) = "Promote31"
    show (Promote32) = "Promote31"
    show (Promote33) = "Promote33"
    show (Pierce) = "Pierce"
    show (Pierce3) = "Pierce3"
    show (Swap) = "Swap"
    show (Swap3) = "Swap3"
    show (First f) = "First " ++ show f
    show (Second f) = "Second " ++ show f
    show (Effect _) = "Effect"
    show (f :>>> g) = "(" ++ show f ++ " >>> " ++ show g ++ ")"
    show (f :*** g) = "[" ++ show f ++ " *** " ++ show g ++ "]"
    show (Loop f) = "Loop " ++ show f
    show (LoopD _ _) = "LoopD"
    show (Init _) = "Init"
    show (Fan f g) = "<" ++ show f ++ " &&& " ++ show g ++ ">"
instance Category (Arr m) where
  id = arr2 id
  (.) = flip (:>>>)

instance Arrow (Arr m) where
    arr = arr2
    first = First
    second = Second
    (***) = (:***)
    (&&&) = Fan
instance ArrowLoop (Arr m) where
    loop = Loop
instance ArrowInit (Arr m) where
    init = Init
class ArrowLoop a => ArrowInit a where
    init :: b -> a b b
instance C.ArrowInit (Arr m) where
    init = Init

draw x = putStrLn $ intercalate "\n\n" $ map show x