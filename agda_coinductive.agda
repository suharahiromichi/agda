{-
  Agda2の Coinductive、余再帰、余代数をつかってみる。
  codataから∞♯♭を使った定義に修正した。
  2012_06_21 @suharahiromichi
-}

module agda_coinductive where

open import Data.Nat
open import Data.List
open import Coinduction                     -- ∞ ♯ ♭
{-
  ♯_ : ∀ {a} {A : Set a} → A → ∞ A     -- \# (not #)
  ♭  : ∀ {a} {A : Set a} → ∞ A → A     -- \b1
-}

{-
  Agda2のcodata, 定義ラシウラさん
  http://d.hatena.ne.jp/bellbind/20080729/1217328830
-}

infixr 5 _::_                               -- Listと区別するために「::」とする。
data Stream (A : Set) : Set where
  _::_ : (x : A) (xs : ∞ (Stream A)) → Stream A

top : {A : Set} -> Stream A -> A
top (h :: _) = h

next : {A : Set} -> Stream A -> Stream A
next (_ :: ts) = ♭ ts

-- 無限に同じデータを繰り返す。
gen : {A : Set} -> A -> Stream A
gen a = a :: ♯ (gen a)

-- mapのStream版
mapf : {A B : Set} -> (A -> B) -> Stream A -> Stream B
mapf f (h :: ts) = (f h) :: ♯ (mapf f (♭ ts))

-- 最初のn個の要素をListで取り出す。
takef : {A : Set} -> (n : ℕ) -> Stream A -> List A
takef zero _ = []
takef (suc n) (h :: ts) = h ∷ takef n (♭ ts)

-- 証明
infix 4 _≡_
data _≡_ {A : Set} (x : A) : A -> Set where
  refl : x ≡ x

{-
  構造比較なので、gen aも next (gen a)も同型と判定され、チェックが通ります。
-}
gen_eq_next_gen : {A : Set}{a : A} -> gen a ≡ next (gen a)
gen_eq_next_gen = refl

-- より直截に (@suharahiromichi)
omega : Stream ℕ
omega = 0 :: (♯ omega)

test0 : takef 3 omega ≡ takef 3 (0 :: (♯ omega))
test0 = refl
-- takefのない一般的な形で証明したい。(see. Coalgebras and Codata in Agda p.15)

-- 無限の自然数列
nats : ℕ -> Stream ℕ
nats n = n :: ♯ (nats (suc n))

test : takef 3 (nats zero) ≡ 0 ∷ 1 ∷ 2 ∷ []
test = refl

test2 : takef 10 (next (nats zero)) ≡ takef 10 (mapf suc (nats zero))
test2 = refl
-- takefのない一般的な形で証明したい。

{-
  Coalgebras and Codata in Agda, Anton Setzer さん
  http://www.cs.swan.ac.uk/~csetzer/slides/wessexSeminarMarch2009.pdf

  coℕでcoListの長さを求める。
-}

data coList (A : Set) : Set where
  [] : coList A                             -- !!!
  _::_ : (x : A) (xs : ∞ (coList A)) → coList A

data coℕ : Set where
  Z : coℕ
  S : ∞ coℕ -> coℕ

colength : {A : Set} -> coList A -> coℕ
colength [] = Z
colength (_ :: xs) = S (♯ colength (♭ xs))

-- lenghtをcoListにしただけでは、停止判定をパスしない（赤くなる）。
len : {A : Set} -> coList A -> ℕ
len [] = zero
len (_ :: xs) = suc (len (♭ xs))

-- END
