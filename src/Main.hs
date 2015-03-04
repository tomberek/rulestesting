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

data ArrM m a b where
    Raise :: ArrM m a (a,())
    Pierce :: ArrM m (a,b) ((a,()),b)
    Pierce3 :: ArrM m (a,b) ((a,()),(a,b))
    Promote31 :: ArrM m (a,b,c) ((a,()),(b,c))
    Promote32 :: ArrM m (a,b,c) ((b,()),(a,c))
    Promote33 :: ArrM m (a,b,c) ((c,()),(a,b))
    Fst :: ArrM m (a,b) a
    Id2 :: ArrM m a a
    Swap :: ArrM m (a,b) (b,a)
    Swap3 :: ArrM m (c,(a,b)) (a,b,c)
    ArrM :: (a -> b) -> ArrM m a b
    FirstM :: ArrM m a b -> ArrM m (a, d) (b, d)
    Second :: ArrM m a b -> ArrM m (d, a) (d, b)
    Effect :: m a b -> ArrM m a b
    (:****) :: ArrM m a b -> ArrM m c d -> ArrM m (a,c) (b,d)
    (:>>>>) :: ArrM m a c -> ArrM m c b -> ArrM m a b
    LoopM :: ArrM m (a, d) (b, d) -> ArrM m a b
    LoopDM :: e -> ((a, e) -> (b, e)) -> ArrM m a b
    InitM :: b -> ArrM m b b
    Fan :: ArrM m a b -> ArrM m a c -> ArrM m a (b,c)

{-# NOINLINE arr2 #-}
arr2 :: (a->b) -> ArrM m a b
arr2 = ArrM

arr3 :: ArrM m (Int,Integer) (Int,Integer)
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

optimized :: Int -> Int
(a,optimized) = $(CCNF.normOpt f)

out :: ArrM m Int Int
out = $(CCNF.norm f)

boring :: ArrM m Int Int
boring = e
main :: IO ()
main = do
    --(runQ $ unTypeQ g) >>= print
    runQ [| (\(CCNF.AExp c) -> c) e |]
    print $ optimized 4
    print out
    print boring
    runQ [arrowExp|
        proc n -> do
        returnA -< 2
        returnA -< n+2
            |]
    print "hi"
    --print $ _
    --print $ f 4
    --print $ e 4
    {-
    
    print "done"
    {-
    --}
    --}
    -- draw $ take 2 $ iterate normalize arrow
{--
type Traversal = forall a b m. ArrM m a b -> ArrM m a b
imap :: Traversal  -> Traversal
imap h (FirstM f) = FirstM (h f)
imap h (f :>>> g) = h f :>>> h g
imap h (Loop f) = Loop (h f)
imap h x = x

norm :: ArrM m a b -> ArrM m a b
norm (Pierce :>>> (FirstM (Fst :>>> f) :>>> Swap)) = FirstM f :>>> Swap
norm ((Pierce3 :>>> (FirstM (Fst :>>> f) :>>> Swap3)) :>>>
     ((Promote31 :>>> (FirstM (Fst :>>> g) :>>> Swap3)) :>>>
     ((Promote31 :>>> (FirstM (Fst :>>> h) :>>> Swap3)) :>>> i))) = ( (Fan f g) :*** h) :>>> ArrM (\((a,b),c) -> (a,b,c)) :>>> i
norm ((FirstM f :>>> Swap) :>>> (FirstM g :>>> Swap)) = f :*** g
norm (Raise :>>> Fst) = Id2
norm (Raise :>>> (Fst :>>> g)) = g
norm (Id2 :>>> g) = g
norm (g :>>> Id2) = g
{-
---}
norm (ArrM f :>>> ArrM g) = ArrM (g . f)           -- original and below
norm (FirstM (ArrM f)) = ArrM (f `cross` id)
norm (ArrM f :>>> LoopD i g) = LoopD i (g . (f `cross` id))
norm (LoopD i f :>>> ArrM g) = LoopD i ((g `cross` id) . f)
norm (LoopD i f :>>> LoopD j g) = LoopD (i,j) (assoc' (juggle' (g `cross` id) . (f `cross` id)))
norm (Loop (LoopD i f)) = LoopD i (trace' (juggle' f))
norm (FirstM (LoopD i f)) = LoopD i (juggle' (f `cross` id))
norm (Loop (ArrM f)) = ArrM (trace' f)
norm (Init i) = LoopD i swap
norm e = e
--normalize ArrowChoice?

everywhere :: Traversal -> Traversal
everywhere h =h. imap (everywhere h)

normalize :: ArrM m a b -> ArrM m a b
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

instance Show (ArrM m a b) where
    show (ArrM _) = "Arr"
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
    show (FirstM f) = "FirstM " ++ show f
    show (Second f) = "Second " ++ show f
    show (Effect _) = "Effect"
    show (f :>>>> g) = "(" ++ show f ++ " >>> " ++ show g ++ ")"
    show (f :**** g) = "[" ++ show f ++ " *** " ++ show g ++ "]"
    show (LoopM f) = "Loop " ++ show f
    show (LoopDM _ _) = "LoopD"
    show (InitM _) = "Init"
    show (Fan f g) = "<" ++ show f ++ " &&& " ++ show g ++ ">"
instance Category (ArrM m) where
  id = arr2 id
  (.) = flip (:>>>>)

instance Arrow (ArrM m) where
    arr = arr2
    first = FirstM
    second = Second
    (***) = (:****)
    (&&&) = Fan
instance ArrowLoop (ArrM m) where
    loop = LoopM
instance ArrowInit (ArrM m) where
    init = InitM
class ArrowLoop a => ArrowInit a where
    init :: b -> a b b
instance C.ArrowInit (ArrM m) where
    init = InitM

draw x = putStrLn $ intercalate "\n\n" $ map show x