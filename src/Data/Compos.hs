{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds #-}
module Data.Compos where
import Control.Applicative
import Data.Monoid
import Data.Functor.Identity

topdown :: (Compos t) => (forall cat a b. t cat a b -> t cat a b) -> t cat a b -> t cat a b
topdown f x = composOp (topdown f) (f x)
topdownM :: (Compos t,Monad m) => (forall cat a b. t cat a b -> m (t cat a b)) -> t cat a b -> m (t cat a b)
topdownM f x = f x >>= composM (topdownM f)
bottomup :: (Compos t) => (forall cat a b. t cat a b -> t cat a b) -> t cat a b -> t cat a b
bottomup f x = f (composOp (bottomup f) x)
bottomupM :: (Compos t,Monad m) => (forall cat a b. t cat a b -> m (t cat a b)) -> t cat a b -> m (t cat a b)
bottomupM f x = composM (bottomupM f) x >>= f

class Compos t where
    compos :: Applicative f => (forall cat1 a1 b1. t cat1 a1 b1 -> f (t cat1 a1 b1)) ->
        t cat a b -> f (t cat a b)

composOp :: Compos t => (forall cat1 a1 b1. t cat1 a1 b1 -> t cat1 a1 b1) -> t cat a b -> t cat a b
composOp f = runIdentity . compos (Identity . f)
composM :: (Compos t,Monad m) => (forall cat1 a1 b1. t cat1 a1 b1 -> m (t cat1 a1 b1)) ->
        t cat a b -> m (t cat a b)
composM f = unwrapMonad . compos (WrapMonad . f)
composMonoid :: (Compos t,Monoid o) => (forall cat1 a1 b1. t cat1 a1 b1 -> o) -> t cat a b -> o
composMonoid f = getConst . compos (Const . f)

{-
topdown :: (Compos t) => (forall cat a b. t cat a b -> t cat a b) -> t cat a b -> t cat a b
topdown f x = composOp (topdown f) (f x)
topdownM :: (Compos t,Monad m) => (forall cat a b. t cat a b -> m (t cat a b)) -> t cat a b -> m (t cat a b)
topdownM f x = f x >>= composM (topdownM f)
bottomup :: (Compos t) => (forall cat a b. t cat a b -> t cat a b) -> t cat a b -> t cat a b
bottomup f x = f (composOp (bottomup f) x)
bottomupM :: (Compos t,Monad m) => (forall cat a b. t cat a b -> m (t cat a b)) -> t cat a b -> m (t cat a b)
bottomupM f x = composM (bottomupM f) x >>= f

class Compos t where
    compos :: Applicative f => (forall cat1 a1 b1. t cat1 a1 b1 -> f (t cat1 a1 b1)) ->
        t cat a b -> f (t cat a b)

composOp :: Compos t => (forall cat1 a1 b1. t cat1 a1 b1 -> t cat1 a1 b1) -> t cat a b -> t cat a b
composOp f = runIdentity . compos (Identity . f)
composM :: (Compos t,Monad m) => (forall cat1 a1 b1. t cat1 a1 b1 -> m (t cat1 a1 b1)) ->
        t cat a b -> m (t cat a b)
composM f = unwrapMonad . compos (WrapMonad . f)
composMonoid :: (Compos t,Monoid o) => (forall cat1 a1 b1. t cat1 a1 b1 -> o) -> t cat a b -> o
composMonoid f = getConst . compos (Const . f)
-}