{-
  Identity Monad モナド
  http://www.slideshare.net/tmiya/typeclass @tamiya_ さん
  p.8 一番簡単ななにもしないIdentityモナドをつくる。  
  
  CoqからAgdaに変換した。
  agda_stdlibの RawMonad をつかい、identity-monadを生成してつかう。
-}

module agda_identity_monad where

open import Data.Nat
open import Data.Bool
open import Data.List
--open import Function                        -- id

----------------------------------
-- Id
--
data Id {a} (A : Set a) : Set a where
  id : (x : A) -> Id A

id' : forall {A} -> A -> Id A
id' x = id x

bind : forall {A B} -> (Id A) -> (A -> Id B) -> Id B
bind (id x) f = f x

----------------------------------
-- Identity Monad
--
open import Category.Monad

identity-monad : forall {A} -> RawMonad (Id {A})
identity-monad = record {
    return = id' ;
    _>>=_  = bind
    }

open RawMonad identity-monad
-- 以下、return と >>= を
-- RawMonad.return identity-monad などと書かなくてよくする。

----------------------------------
-- モナド則の証明
--
infixr 4 _==_
_==_ : forall {A : Set} -> A -> A -> Set1
a == b = (P : _ -> Set) -> P a -> P b

eqrefl : forall {A : Set} {x : A} -> x == x
eqrefl _ p = p

-- 実際の証明

mr1 : forall {A} (x : A) (f : A -> Id A) ->
  ((return x) >>= f) == (f x)
mr1 f x = eqrefl

mr2 : forall {A} (mx : Id A) ->
  (mx >>= return) == mx
mr2 (id x) = eqrefl

mr3 : forall {A} (mx : Id A) (f g : A -> Id A) ->
  ((mx >>= f) >>= g) == (mx >>= (\ x -> (f x >>= g)))
mr3 (id x) _ _ = eqrefl

-- END
