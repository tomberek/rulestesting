{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ViewPatterns #-}
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
import           Control.Arrow.TH
import           Control.Arrow hiding ((&&&),(***),first,second)
import           Control.Concurrent          (threadDelay)
import Control.Concurrent.Async
import           Data.Time
import           Network.HTTP
import Prelude hiding (id,(.),fst,snd)
import Control.Category
import Control.Category.Associative
import Control.Category.Structural
import Control.Category.Monoidal
import Control.Category.Cartesian
import Control.Categorical.Bifunctor
import Language.Haskell.TH.Utilities
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Quote
import Language.Haskell.TH.Lib
import Language.Haskell.Meta.Parse
import Data.Generics
import Control.Applicative
import Control.Arrow.CCA.Rules
import qualified Language.Haskell.Exts as E
import Language.Haskell.Meta.Utils
import qualified Control.Lens as L
import Control.Category.Rules
{-
line1 :: (Arrow a,Category a,ArrowCCA a) => a b b
line1 = [arrow| proc g -> do
            id -< g|]

line2 :: (HasTerminal a,Category a) => a Int ()
line2 = [arrow| proc g -> id -< () |]

line3 :: (Weaken (,) a,Category a,ArrowCCA a) => a (Int,Int) Int
line3 = [arrow| proc (x,y) -> do
            id -< x |]
---}
line4 :: (Weaken (,) a,Contract (,) a,Category a,ArrowCCA a) => a (Int,Int) Int
line4 = [catCCA| proc (x,y) -> do
             z <- arr(*2) -< x+1
             w <- id -< y
             id -< z+w
             |]


{-
line5 :: ArrowCCA a => a (Maybe c) c
line5 = [arrow| proc (Just a) -> id -< a |]
{-
line5 :: (Weaken (,) a,Category a) => a (Int,Int) Int
line5 = [arrow| proc (x,y) -> do
            z <- id -< x
            id -< (z,y)
            |]
---}

{-
processURL :: String -> IO String
processURL a = do
    getCurrentTime >>= print
    threadDelay 1000000
    response <- simpleHTTP (getRequest a)
    getResponseBody response

getURLSum :: (M a ~ IO,ArrowCCA a) => a String Int
getURLSum = [arrow| (arrM processURL) >>> (arr length) |]

line2 :: (M a ~ IO, ArrowCCA a,Weaken (,) a,Symmetric (,) a,Contract (,) a) => a (String,String) Int
line2 = [arrow|
    proc (x,y) -> do
        a <- getURLSum -< y
        b <- getURLSum -< x
        returnA -< a+b
    |]
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

line3a :: (HasTerminal () a, Symmetric (,) a,HasIdentity () (,) a,Weaken (,) a,Contract (,) a,ArrowCCA a) => a (b,c) (c,())
line3a = [arrow|
    proc (a,b) -> do
        f <- terminate -< a
        g <- id -< b
        id -< (g,f)
        |]
{-
line3a :: (HasTerminal () a,Symmetric (,) a,HasIdentity () (,) a,Weaken (,) a,ArrowCCA a) => a (c,b) ((),())
line3a = [arrow|
    proc (a,b) -> do
        (c,d) <- swap -< (a,b)
        (e,f) <- terminate *** terminate -< ((),())
        (g,h) <- swap -< (c,e)
        (i,j) <- swap -< (f,d)
        (m,n) <- terminate *** terminate -< ((),())
        (k,l) <- terminate *** terminate -< ((),())
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
{-
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
instance Arrow Bij where
    arr = error "used arr"
    first (Bij a b) = Bij (\(c,d)->(a c,d)) (\(e,f)->(b e,f))
instance ArrowLoop Bij where
    loop = undefined
instance ArrowCCA Bij where
    --arr' = error "used arr'"
    delay = undefined
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
---}
{-
step1 :: ArrowCCA a => a T1 T3
step1 = [arrow|
    proc (t1,()) -> do
    Right (t0,t2) <- Lift tree -< t1
    Right (t1',t3) <- Lift tree -< t2
    returnA -< (t3,t1')
    |]
iso :: Bij Tree Tree
iso = [arrow|
    proc t1 -> do
    (t0, t2) <- tree -< t1
    (t1', t3) <- tree -< t2
    (t2', t4) <- tree -< t3
    (t3', t5) <- tree -< t4
    (t4', t6) <- tree -< t5
    (t5', t7) <- tree -< t6

    t4'' <- inverse tree -< (t3', t5')
    t3'' <- inverse tree -< (t2', t4'')
    t2'' <- inverse tree -< (t1', t3'')
    t1'' <- inverse tree -< (t0, t2'')

    -- still in scope: t1'',  t4',  t7

    (t6', t8) <- tree -< t7
    (t5'', t7') <- tree -< t6'
    (t4''', t6'') <- tree -< t5''
    (t3''', t5''') <- tree -< t4'''

    -- still in scope: t1'', t3''', t4''',t5''',t6'',t7',t8

    t2''' <- inverse tree -< (t1'', t3''')
    t3'''' <- inverse tree -< (t2''', t4''')
    t4'''' <- inverse tree -< (t3'''', t5''')
    t5'''' <- inverse tree -< (t4'''', t6'')
    t6''' <- inverse tree -< (t5'''', t7')
    t7'' <- inverse tree -< (t6''', t8)

    returnA -< t7''
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
{- no implemented yet
example1 :: ArrowCCA a => a Int Int
example1 = [arrow|
    proc n -> do
        a  <- arr (\x -> x) -< (n::Int)
        rec
            e <- arr (+1) -< a + (1::Int)
        returnA -< a
    |]
-}
---}


{-
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
example2 = [arrow|
    proc n -> do
        b <-  arr (+1) -< n+2*3
        e <-  arr (+2) -< n
        c <-  arr (+3) -< b
        d <-  arr (uncurry (+)) -< (c,e)
        arr (uncurry (-)) -< (n,d)
            |]
---}
---}

{- no implemented yet
example1 :: ArrowInit a => a Int Int
example1 = [arrow|
    proc n -> do
        a  <- arr (\x -> x) -< (n::Int)
        rec
            e <- arr (+1) -< a + (1::Int)
        returnA -< a
    |]


{-
i :: ArrowCCA a => a Int Int
i = [arrow|
    proc n -> do
        x <- arr id -< n
        y <- arr (+1) -< x
        let z = x+y
        returnA -< z
        |]

---}
---}
