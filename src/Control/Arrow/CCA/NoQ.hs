{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE TypeFamilies               #-}
{- |
Module      :  Control.Arrow.CCA
Description :  ArrowDelay
Copyright   :  (c) 2015 Thomas Bereknyei
License     :  BSD3
Maintainer  :  Thomas Bereknyei <tomberek@gmail.com>
Stability   :  unstable
Portability :  MultiParamTypeClasses

Originally from CCA package: <https://hackage.haskell.org/package/CCA-0.1.5.2>

Added ArrowEffect in order to model effectful arrows.
Adding Swap,Id,Dup,Diag for CCC normalization
-}
module Control.Arrow.CCA.NoQ where

import           Control.Arrow
import           Control.Category         (Category)
import           Control.Concurrent.Async
import           Control.Monad.Identity
import           Language.Haskell.TH

import Control.Categorical.Bifunctor (Bifunctor,(***),PFunctor,QFunctor)
import Control.Category.Structural (Weaken)
import qualified Control.Category.Structural (Weaken(..))
-- | An @'ArrowCCA'@ is a typeclass that captures causual commutative arrows.
-- Any instance must also be an instance of 'ArrowLoop'.
-- Merged at the moment with an @'ArrowEffect'@ typeclass that captures monadic
-- causual commutative arrows.
-- Laws:
-- `first f >>> second g == second g >>> first f`
-- `init i *** init j == init (i,j)`
instance ArrowCCA (->) where
    delay = error "undefined delay for -> "
class (ArrowLoop a,Weaken (,) a) => ArrowCCA a where
    {-# NOINLINE arr' #-}
    arr' :: Exp -> (b->c) -> a b c
    arr' _ = arr
    delay :: b -> a b b
    delay' :: Exp -> b -> a b b
    delay' _ = delay
    loopD :: e -> ((b, e) -> (c, e)) -> a b c
    loopD i f = loop (arr f >>> second (delay i))
    type M a :: * -> *
    type M a = Identity
    arrM :: (b -> (M a) c) -> a b c
    default arrM :: (b -> Identity c) -> a b c
    arrM f = arr $ \a -> runIdentity $ f a
    arrM' :: Exp -> (b -> (M a) c) -> a b c
    arrM' _ = arrM

class Category k => HasTerminal k where
                            terminate :: i -> k a i
                            terminate' :: Exp -> i -> k a i
                            terminate' _ = terminate
instance HasTerminal (->) where
    terminate = const
instance Monad m => Weaken (,) (Kleisli m) where
    fst = Kleisli $ return . fst
    snd = Kleisli $ return . snd
instance Monad m => Bifunctor (,) (Kleisli m) where
    (***) (Kleisli f) (Kleisli g) = Kleisli $ \(a,b) -> do
        a' <- f a
        b' <- g b
        return (a',b')
instance Monad m => PFunctor (,) (Kleisli m)
instance Monad m => QFunctor (,) (Kleisli m)

newtype PKleisli a b = PKleisli {runPKleisli :: Kleisli IO a b} deriving (Category,ArrowLoop,Weaken (,),Bifunctor (,),PFunctor (,),QFunctor (,))
rr :: PKleisli a b -> a -> IO b
rr = runKleisli . runPKleisli
instance Arrow (PKleisli) where
    arr = PKleisli . arr
    first (PKleisli f) = PKleisli $ first f
    a1 *** a2 = PKleisli $ Kleisli $ \(x1, x2) -> do
         ( y1, y2 ) <- concurrently (rr a1 x1) (rr a2 x2)
         return  (y1, y2)

instance ArrowCCA (PKleisli) where
    delay = error "delay for PKleisli not defined"
    type M PKleisli = IO
    arrM f = PKleisli $ Kleisli f

instance MonadFix m => ArrowCCA (Kleisli m) where
    delay = error "delay for PKleisli not defined"
    type M (Kleisli m) = m
    arrM f = Kleisli f
