{--
  等号の意味について。

  圏論でCoq
  http://d.hatena.ne.jp/m-a-o/20110325/p1

  型理論での形式的証明記述の技法について(agda1)
  http://www.nue.riec.tohoku.ac.jp/jssst2005/papers/05061.pdf  
  
  "The Inadequacy of Pure Intention"、Ryan Wisnesky Paul Govereau、Harvard School of Something
  この論文は、途中でCoqにも言及している。
--}

module agda_equality4 where

open import Level

{-
deﬁnitional equality（intentional equality、≡）とpropositional equality（extensional equality、==）がある。

deﬁnitional equalityとはβ簡約で一緒になるということでよいようだ。

propositional equalityは、ライプニッツの外延性を満たす（extensionally equivalent in the sense of Leibniz）ので、
Leibniz equalityと同じもののと考えてよい。

deﬁnitional equalityなら、propositional equalityである。逆は成立しない。
-}

------------------------------------------------------
-- deﬁnitional equality（intentional equality、≡）

data id {A : Set} : A -> A -> Set where
  refl : (a : A) -> id a a               -- は、{a : A} としてもよい。

data id' {n} {A : Set n} : A -> A -> Set n where
  refl : (a : A) -> id' a a              -- は、{a : A} としてもよい。

data id'' {A : Set} (x : A) : A -> Set where
  refl : id'' x x

-- Agda_stdlib/Relation/Binary/Core.agda における(≡)。
-- Propositional equality
data ≡ {a} {A : Set a} (x : A) : A -> Set a where
  refl : ≡ x x

------------------------------------------------------
-- propositional equality（extensional equality、==）
-- CoqのLeibnitz equality。Set1ではなくPropとする。
data eq {A : Set} (x : A) : A -> Set1 where
  refl : eq x x

data eq' {A : Set} : A -> A -> Set1 where
  refl : (a : A) -> eq' a a              -- は、{a : A} としてもよい。

data eqn {a} {A : Set a} (x : A) : A -> Set (suc a) where
  refl : eqn x x

-- Algebraic Reasoning における(==)。
-- Agda1ではSet1はTypeとする。
-- これは、Coqの定義とおなじ。
-- ただしい形ののLeibnitz equality。
-- CoqではSet1ではなくPropとする。
_==_ : forall {A : Set} -> A -> A -> Set1
a == b = (P : _ -> Set) -> P a -> P b

eqrefl : forall {A : Set} {x : A} -> x == x
eqrefl _ p = p

--------------------------------------------------
-- 証明
--
-- Leibnitz equality の定義が同値かとうか？
-- とくに eq と ==
--
lemm1 : {A : Set} (a b : A) -> a == b -> eq a b
lemm1 = ?

lemm2 : {A : Set} (a b : A) -> eq a b -> a == b
lemm2 = ?

lemm3 : {A : Set} (a b : A) (P : A -> Set1) -> eq a b -> P b
lemm3 = ?

--
-- Leibnitz equalityがライプニッツの外延性を満たすことの証明
--
--lemm : {X Y : Set} {x : X} {f g : X -> Y} -> f == g -> f x == g x
--lemm eqrefl = ?

-- END
