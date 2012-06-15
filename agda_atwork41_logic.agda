{-
  Dependent Types at Work
  Ana Bove and Peter Dybjer

  4. Propositions as Types の前半部分
  
  Brouwer-Heyting-Kolmogorov (BHK)-interpretation of logic, as reﬁned
  and formalised by Martin-Lof.
-}

module agda_atwork41_logic where

-----------------------------
-- 4.1 Propositional Logic
-----------------------------

-- ∧-introduction
-- Coq:
-- ゴールがA/\Bのとき、split == apply conj。
-- つまり、コンストラクタconjを適用する。
data _∧_ (A B : Set) : Set where
  conj : A -> B -> A ∧ B                   -- <_,_>
-- BHK解釈:
-- A∧Bの証明は、conj a b、
-- ここで、aはAの証明、bはBの証明。

-- ∧-elimination
-- Coq:
-- 前提がA/\Bのとき、destruct や case を使って分解することができる。
-- destruct H1 as [ HA HB ].
-- 関数定義のなかに、直接match withが書かれ、以下のような関数は用意されない。
fst : {A B : Set} -> A ∧ B -> A
fst (conj a b) = a

snd : {A B : Set} -> A ∧ B -> B
snd (conj a b) = b

-- ∨-introduction
-- Coq:
-- ゴールがA∨Bのとき、left または right
-- left == apply or_intror == constructor 1
-- right == apply or_introl == constructor 2
-- つまり、or_introlまたは、or_introllを適用する。
data _∨_ (A B : Set) : Set where
  or_introl : A -> A ∨ B                   -- inl
  or_intror : B -> A ∨ B                   -- inr
-- BHK解釈:
-- A∨Bの証明には、Aの証明(or_introl a)または、
-- Bの証明(or_intror b)のどちらかが、あればよい。
-- どちらがあるかは、コンストラクタが、or_introlかor_ontrorかを
-- をみて振り分けないといけない。次のcase関数。

-- ∨-elimination
-- Coq:
-- 前提がA\/Bのとき、destruct や case を使って分解することができる。
-- destruct H1 as [ HA | HB ].
-- 関数定義のなかに、直接match withが書かれ、以下のような関数は用意されない。
case : {A B C : Set} -> A ∨ B -> (A -> C) -> (B -> C) -> C
case (or_introl a) d e = d a
case (or_intror b) d e = e b

-- Trueの定義
-- Coq:
-- Inductive True := I.
data True : Set where
  tt : True                                 -- 唯一の値

-- Falseの定義
-- Coq:
-- Inductive False := .
data False : Set where                      -- 空集合

-- ⊥-elimination
-- Coq:
-- ゴールがFalseのとき、Falseはコンストラクタを持たないため、
-- この型を持つ値は存在しない。よって、
-- 前提から False を導かない限りこれを証明することはできない。
falseElim : {A : Set} -> False -> A
falseElim ()

-- ~-elimination
-- Coq:
-- ゴールが~Bのとき、これは、B->Falseであるから、
-- introで、Bを前提に移動し、Falseを証明する。
~ : Set -> Set                              -- Not
~ A = A -> False

-- ⇒-elimination
-- Coq:
-- ゴールがA⟹Bのとき、introで、⟹の仮定Aを前提に移動する。
_==>_ : (A B : Set) -> Set
A ==> B = A -> B

-- <==>-elimination
_<==>_ : Set -> Set -> Set
A <==> B = (A ==> B) ∧ (B ==> A)

-----------------------------
-- 4.2 Predicate Logic
-----------------------------

-- ∀-introduction
-- Coq:
-- ゴールが∀x:A,Bのとき、introで、x:Xを前提に移動する。
Forall : (A : Set) -> (B : A -> Set) -> Set
Forall A B = (x : A) -> B x

-- ∃-introduction
-- Coq:
-- ゴールが∃a:A,Bのとき、コンストラクタex_introを適用するが、
-- a : A なる aの値を明示しないといけない。
data ex (A : Set) (B : A -> Set) : Set where
  ex_intro : (a : A) -> B a -> ex A B
-- 原論文のagdaコード:
-- data Exists (A : Set) (B : A -> Set) : Set where
--   exists : (a : A) -> B a -> Exists A B

-- ∃-elimination
-- Coq:
-- 前提が∃a:A,Bのとき、destruct や case を使って分解することができる。
-- destruct HB as [ a HBB ].
-- 関数定義のなかに、直接match withが書かれ、以下のような関数は用意されない。
-- ∃a:A,Bのaを取り出す場合。
witness : {A : Set} {B : A -> Set} -> ex A B -> A
witness (ex_intro a b) = a

-- ∃a:A,Bのbを取り出す場合。
proof : {A : Set} {B : A -> Set} -> (p : ex A B) -> B (witness p)
proof (ex_intro a b) = b

---------------------
-- Martin-Lof deﬁnes ...
---------------------
-- Martin-Lof deﬁnes implication as a set with one constructor:
data _==>’_ (A B : Set) : Set where
  fun : (A -> B) -> A ==>’ B

-- In this way, a canonical proof of A ==>’ B always begins with the
-- constructor fun. The rule of ==>’-elimination (modus ponens) is now
-- deﬁned by pattern matching:
apply : {A B : Set} -> A ==>’ B -> A -> B
apply (fun f) a = f a

-- Martin-Lof deﬁnes the universal quantiﬁer as a set with one constructor:
data Forall’ (A : Set) (B : A -> Set) : Set where
  forallI : ((a : A) -> B a) -> Forall’ A B

-- ∀-elimination (Exercise)
forallElim : {A : Set}{a : A}{B : A -> Set} -> (Forall’  A B) -> B a
forallElim {A} {a} {B} (forallI x) = x a

-- END
