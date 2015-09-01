{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE QuasiQuotes     #-}
{-# LANGUAGE TypeFamilies    #-}
{-# LANGUAGE LambdaCase    #-}
module Examples where
import           Control.Arrow.CCA.Optimize
import           Control.Arrow.TH
import           Control.Arrow
import           Control.Concurrent          (threadDelay)
import Control.Concurrent.Async
import           Data.Time
import           Network.HTTP
import Prelude hiding (id,(.))
import Control.Category
{-
line1 :: (M a ~ IO,ArrowCCA a) => a (String, String) ()
line1 = [arrow| proc (n,g) -> do
    a <- getURLSum -< n
    d <- getURLSum -< g
    b <- arr length -< n
    c <- arrM (\input -> do
               print input
               print ":"
               read <$> getLine) -< n
    _ <- arrM print -< a + c + d
    returnA -< ()
    |]
---}

processURL :: String -> IO String
processURL a = do
    getCurrentTime >>= print
    threadDelay 1000000
    response <- simpleHTTP (getRequest a)
    getResponseBody response

getURLSum :: (M a ~ IO,ArrowCCA a) => a String Int
getURLSum = [arrow| (arrM processURL) >>> (arr length) |]

line2 :: (M a ~ IO, ArrowCCA a) => a (String,String) Int
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
line3 :: ArrowCCA a => a (b,c) (b,c)
line3 = [arrow|
    proc (a,b) -> do
        (c,d) <- arr (\(a,b)->(b,a)) -< (a,b)
        (e,f) <- arr (const ((),())) -< ()
        (g,h) <- arr (\(a,b)->(b,a)) -< (c,e)
        (i,j) <- arr (\(a,b)->(b,a)) -< (d,f)
        () <- arr (const ()) -< (g,i)
        (l,m) <- arr (\(a,b)->(b,a)) -< (h,j)
        returnA -< (l,m)
        |]
line3a :: ArrowCCA a => a (c,b) ((),())
line3a = [arrow|
    proc (a,b) -> do
        (c,d) <- arr swap -< (a,b)
        (e,f) <- arr (const ((),())) -< ()
        (g,h) <- arr swap -< (c,e)
        (i,j) <- arr swap -< (f,d)
        (m,n) <- arr (const ((),())) -< ()
        (k,l) <- arr (const ((),())) -< ()
        (q,r) <- arr swap -< (h,k)
        (s,y) <- arr swap -< (l,i)
        (o,p) <- arr swap -< (n,g)
        (t,u) <- arr swap -< (p,q)
        (v,w) <- arr swap -< (r,s)
        (x,z) <- arr swap -< (y,j)
        () <- arr (const ()) -< (o,t)
        () <- arr (const ()) -< (u,v)
        () <- arr (const ()) -< (w,x)
        returnA -< (m,z)
    |]
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
step1 :: ArrowCCA a => a T1 T3
step1 = [arrow|
    proc (t1,()) -> do
    Right (t0,t2) <- Lift tree -< t1
    Right (t1',t3) <- Lift tree -< t2
    returnA -< (t3,t1')
    |]
{-
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
---}
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


example4 :: ArrowCCA a => a Int Int
example4 = [arrow|
     proc n -> do
        a <- arr (+1) -< n
        returnA -< n
        _ <- arr (*2) -< n+1
        d <- arr (*2) -< a*1
        returnA -< n
            |]
example4b :: ArrowCCA a => a Int Int
example4b = [arrow|
     proc n -> do
        d <- arr (uncurry (+)) -< (n,n)
        arr (uncurry (-)) -< (n,d)
            |]
example2 :: ArrowCCA a => a Int Int
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
