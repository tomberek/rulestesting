{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE QuasiQuotes     #-}
{-# LANGUAGE TypeFamilies    #-}
{-# LANGUAGE LambdaCase    #-}
{-# LANGUAGE AllowAmbiguousTypes    #-}
module Examples where
import           Control.Arrow.CCA
import           Control.Arrow hiding ((&&&),(***),first,second)
import           qualified Control.Arrow
import           Control.Concurrent          (threadDelay)
import Control.Concurrent.Async
import           Data.Time
import           Network.HTTP
import Prelude hiding (id,(.),fst,snd)
import Control.Category
import Control.Category.Rules(cat)
import Control.Category.Associative
import Control.Category.Structural
import Control.Category.Structural.Rules
import Control.Categorical.Bifunctor
import Language.Haskell.TH.Syntax
import Control.Arrow.CCA.Rules
import Control.Arrow.CCA.Free(arrow,category)


line1 :: (Category a) => a b b
line1 = [structural| proc g -> do
             id -< g|]

line2 :: (HasTerminal a,Category a) => a Int ()
line2 = [structural| proc g -> id -< () |]

line3 :: (Weaken (,) a,Category a) => a (Int,Int) Int
line3 = [structural| proc (x,y) -> do
            line1 -< x |]
---}

line4 :: (Weaken (,) a,Contract (,) a,Category a,ArrowCCA a,Symmetric (,) a) => a (Int,Int) Int
line4 = [catCCA| proc (x,y) -> do
              z <- arr (*2) -< x+1
              id -< (z+y)
              |]

line5 :: ArrowCCA a => a (Maybe c) c
line5 = [structural| proc (Just a) -> id -< a |]

line6 :: (Category a) => a (Int,Int) (Int,Int)
line6 = [catCCA| proc (x,y) -> do
            z <- id -< x
            id -< (z,y)
            |]

processURL :: String -> IO String
processURL a = do
    getCurrentTime >>= print
    threadDelay 1000000
    response <- simpleHTTP (getRequest a)
    getResponseBody response

getURLSum :: (M a ~ IO,ArrowCCA a) => a String Int
getURLSum = [catCCA| (arrM processURL) >>> (arr length) |]

line7 :: (M a ~ IO,ArrowCCA a,Weaken (,) a,Symmetric (,) a,Contract (,) a) => a (String,String) Int
line7 = [catCCA|
    proc (x,y) -> do
        a <- getURLSum -< y
        b <- getURLSum -< x
        returnA -< a+b
    |]
---}
        {-
    (e,f) <- cap ()
    (g,h) <- over (c,e)
    (i,j) <- over (f,d)
    (m,n) <- cap ()
    (k,l) <- cap ()
    (q,r) <- over (h,k)
    (s,y) <- over (l,i)
    (o,p) <- over (n,g)
    (t,u) <- under (p,q)
    (v,w) <- under (r,s)
    (x,z) <- over (y,j)
    () <- cup (o,t)
    () <- cup (u,v)
    () <- cup (w,x)
    -}

line8 :: (HasTerminal a, Symmetric (,) a,Contract (,) a,Weaken (,) a) => a (b,c) (c,())
line8 = [catCCA|
    proc (a,b) -> do
        f <- terminate () -< a
        g <- id -< b
        id -< (g,f)
        |]

temp :: (Associative (,) a,Contract (,) a,Weaken (,) a) => a ((b,c),d) (c,d)
temp = [structural|
    proc n -> associate >>> snd -< n
    |]

{-
line9 :: (Associative (,) a,HasTerminal a,Symmetric (,) a,HasIdentity () (,) a,Weaken (,) a,ArrowCCA a,Contract (,) a) => a (c,b) ((),())
line9 = [catCCA|
    proc (a,b) -> do
        (c,d) <- swap -< (a,b)
        (e,f) <- terminate () *** terminate () -< ((),())
        (g,h) <- swap -< (c,e)
        (i,j) <- swap -< (f,d)
        (m,n) <- terminate () *** terminate () -< ((),())
        (k,l) <- terminate () *** terminate () -< ((),())
        (q,r) <- swap -< (h,k)
        (s,y) <- swap -< (l,i)
        (o,p) <- swap -< (n,g)
        (t,u) <- swap -< (p,q)
        (v,w) <- swap -< (r,s)
        (x,z) <- swap -< (y,j)
        id -< (o,t)
        id -< (u,v)
        id -< (w,x)
        id -< (m,z)
    |]
---}

---}
data Bij a b = Bij (a->b) (b->a)
inverse :: Bij a b -> Bij b a
inverse (Bij a b) = Bij b a
instance Category Bij where
    id = Bij id id
    Bij a b . Bij c d = Bij (a.c) (d.b)
data Tree = Leaf | Branch Tree Tree
tree :: Bij (Tree,t) (Either t (Tree,(Tree,t)))
tree = Bij (\case
               (Leaf,x) -> Left x
               (Branch a b,x) -> Right (a,(b,x)))
           (\case
               Left x -> (Leaf,x)
               Right (a,(b,x)) -> (Branch a b,x))
instance Bifunctor Either Bij where
    (Bij a b) *** (Bij f g) = Bij (\case
                     Left x -> Left $ a x
                     Right y -> Right $ f y)
                     (\case
                         Left x -> Left $ b x
                         Right y -> Right $ g y)
instance PFunctor Either Bij
instance QFunctor Either Bij
instance Symmetric Either Bij where
    swap = Bij swap swap
instance Associative Either Bij where
    associate = Bij associate coassociate
    coassociate = Bij coassociate associate
type T = Tree
type T0 = ()
type T1 = (T,T0)
type T2 = (T,T1)
type T3 = (T,T2)
type T4 = (T,T3)
type T5 = (T,T4)
type T6 = (T,T5)
type T7 = (T,T6)
type T8 = (T,T7)


iso2 :: Bij T1 T7
iso2 = [structural|
    proc (ta,tb) -> do
    (t0,t2') <- tree -< (ta,tb)
    (t1,t3') <- tree -< t2'
    (t2,t4') <- tree -< t3'
    (t3,t5) <- tree -< t4'
    (t4,t6') <- tree -< t5
    (t5',t7') <- tree -< t6'


    t4'' <- inverse tree -< (t3,t5')
    t3'' <- inverse tree -< (t2,t4'')
    t2'' <- inverse tree -< (t1,t3'')
    t1'' <- inverse tree -< (t0,t2'')

    (t6''', t8) <- tree -< t7'
    (t5''', t7f) <- tree -< t6'''
    (t4''', t6f) <- tree -< t5'''
    (t3''', t5f) <- tree -< t4'''


    t2'''' <- inverse tree -< (t1'',t3''')
    t3'''' <- inverse tree -< (t2'''',t4)
    t4'''' <- inverse tree -< (t3'''',t5f)
    t5'''' <- inverse tree -< (t4'''',t6f)
    t6'''' <- inverse tree -< (t5'''',t7f)
    t7'''' <- inverse tree -< (t6'''',t8)
    returnA -< t7''''
    |]
data KnotSection a b where
   Line  :: KnotSection a a
   Over  :: KnotSection (a,b) (b,a)
   Under :: KnotSection (a,b) (b,a)
   Cap :: KnotSection () (a,a)
   Cup :: KnotSection (a,a) ()
   Knot :: KnotSection () ()
instance Category KnotSection where
    id = Line
    Line . f = f
    f . Line = f
    Over . Over = Line
    Over . Under = Line
    Under . Over = Line
    Cup . Cap = Knot
instance Arrow KnotSection where
    arr = undefined
    first = undefined
instance ArrowLoop KnotSection where
    loop = error "not defined"
instance ArrowCCA KnotSection where
    delay = error "not defined"
example1' :: Arrow a => a Int Int
example1' = [arrow|
    proc n -> do
        a  <- arr (\x -> x) -< (n::Int)
        rec
            e <- arr (+1) -< a + (1::Int)
        returnA -< a
    |]
example4 :: ArrowCCA a => a Int Int
example4 = [arrow|
     proc n -> do
        a <- arr (+1) -< n
        returnA -< n
        _ <- arr (*2) -< n+1
        d <- arr (*2) -< a*1
        returnA -< n
            |]
example4b :: (Symmetric (,) a,Contract (,) a,ArrowCCA a) => a Int Int
example4b = [arrow|
     proc n -> do
        d <- arr (uncurry (+)) -< (n,n)
        arr (uncurry (-)) -< (n,d)
            |]


example2 :: (Symmetric (,) a,Contract (,) a,ArrowCCA a) => a Int Int
example2 = _ $ [structural|
    proc x -> do
            y <- f -< x+1
            g -< 2*y
            let z = x+y
            t <- h -< x*z
            returnA -< t+z
            |]
    where f = arr' [| ((*) 999) |] ((*) 999)
          h = arr' [| ((*) 888) |] ((*) 888)

---}
{-
should be
arr (\ x -> (x+1, x)) >>>
        first f >>>
        arr (\ (y, x) -> (2*y, (x, y))) >>>
        first g >>>
        arr (\ (_, (x, y)) -> let z = x+y in (x*z, z)) >>>
        first h >>>
        arr (\ (t, z) -> t+z)
---}
example1 :: ArrowCCA a => a Int Int
example1 = [catCCA|
    proc n -> do
        a  <- arr (\x -> x) -< (n::Int)
        rec
            e <- arr (+1) -< a + (1::Int)
            b <- delay 0 -< e
        returnA -< b
    |]

i :: ArrowCCA a => a Int Int
i = [catCCA|
    proc n -> do
        x <- arr id -< n
        y <- arr (+1) -< x
        let z = x+y
        returnA -< z
        |]
---}
---}
