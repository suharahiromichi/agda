{--
  tmiyaさんの練習問題をラムダ式で解いてみた
  2012_05_17

　以下をもとに、agdaの特徴であるパターンマッチをつかって改良した。
  http://d.hatena.ne.jp/zyxwv/20100928/1285676648
  
  パターンは、coqでの実装を参考にした、というより同じものである。
  http://d.hatena.ne.jp/yoshihiro503/20100926
--}

module agda_tamiya where

data True : Set where
  tt : True
data False : Set where
-- 空集合

infixl 10 _∧_
data _∧_ (P Q : Set) : Set where
  and-intro : P -> Q -> P ∧ Q              -- space必須

and-eliml : forall {P Q} -> P ∧ Q -> P
and-eliml (and-intro y y') = y

and-elimr : forall {P Q} -> P ∧ Q -> Q
and-elimr (and-intro y y') = y'

infixl 9  _∨_
data _∨_ (P Q : Set) : Set where
  or-introl : P -> P ∨ Q                   -- space必須
  or-intror : Q -> P ∨ Q                   -- space必須

or-elim : forall {P Q R : Set} -> (P ∨ Q) -> (P -> R) -> (Q -> R) -> R
or-elim (or-introl y) a b = a y
or-elim (or-intror y) a b = b y

~_ : Set -> Set
~ p = p -> False

lemma01 : forall (A B C : Set) -> (A -> B -> C) -> (A -> B) -> A -> C
lemma01 a b c d e f = d f (e f)

lemma02 : forall A B C -> A ∧ (B ∧ C) -> (A ∧ B) ∧ C
lemma02 a b c (and-intro ha (and-intro hb hc)) =
  and-intro (and-intro ha hb) hc

lemma03 : forall A B C D -> (A -> C) ∧ (B -> D) ∧ A ∧ B -> C ∧ D
lemma03 a b c d (and-intro (and-intro (and-intro h1 h2) ha) hb) =
  and-intro (h1 ha) (h2 hb)

lemma04 : forall A -> ~ (A ∧ ~ A)
lemma04 a (and-intro ha hna) = hna ha

lemma05 : forall A B C -> A ∨ (B ∨ C) -> (A ∨ B) ∨ C
lemma05 a b c (or-introl ha) = or-introl (or-introl ha)
lemma05 a b c (or-intror (or-introl hb)) = or-introl (or-intror hb)
lemma05 a b c (or-intror (or-intror hc)) = or-intror hc

lemma06 : forall A -> ~ ~ ~ A -> ~ A
lemma06 a b c = b (\ x -> x c)

lemma07 : forall A B -> (A -> B) -> ~ B -> ~ A
lemma07 a b c d e = d (c e)

lemma08 : forall (A B : Set) -> ((((A -> B) -> A) -> A) -> B) -> B
lemma08 a b c = c (\ x -> x (\ x' -> c (\ _ -> x')))

lemma09 : forall A -> ~ ~ (A ∨ ~ A)
lemma09 a b = b (or-intror (\ x -> b (or-introl x)))

-- END
