{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
module Control.Category.Monoidal where
import           Control.Category
import           Prelude             hiding (id, (.))
import Data.Bifunctor

data Skew b c where
    Id :: Skew b c
    X' :: Skew a b -> Skew c d -> Skew (a,b) (c,d)

data Tm a = I | X a  | Tm a :-: Tm a deriving Show
data Nf a = J | Tm a :.: Nf a deriving Show

data Rules = IdRule | Dot Rules Rules | Cross Rules Rules | Lam | Rho | Asc deriving Show

emb :: Nf a -> Tm a
emb J = I
emb (X a :.: nf) = X a :-: emb nf

splay :: Tm a -> Nf a -> Nf a
splay (X x) n = X x :.: n
splay I n = n
splay (a :-: b) n = splay a (splay b n)

nf :: Tm a -> Nf a
nf a = splay a J

splat :: Tm a -> Nf a -> Rules
splat (X _) _ = IdRule
splat I _ = Lam
splat (a :-: b) n = ((splat a $ splay b n) `Dot` IdRule) `Cross` ((splat b n) `Dot` Asc)

nm :: Tm a -> Rules
nm a = (splat a J) `Dot` Rho

data Objects = A | B | C deriving Show
a = nf t
t = ( I :-: X A :-: I :-: X B)
b = nm t


