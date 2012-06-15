{--
  等号の定義、リストをrevしても同じことの証明
  等号の定義は、
  http://www.slideshare.net/ikegami__/agda-proofsummit-2011
  p.92 あたりから。
--}

module agda_equality where

-- Leibnitz equality
data _≡_ {A : Set} (x : A) : A -> Set where
  refl : x ≡ x

-- 等号の遷移則
trans : {A : Set} -> {x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
trans refl refl = refl

trans3 : {A : Set} -> {x y z u : A} -> x ≡ y -> y ≡ z -> z ≡ u -> x ≡ u
trans3 refl refl refl = refl

-- 等号の反射則
sym : {A : Set} -> {x y : A} -> x ≡ y -> y ≡ x
sym refl = refl

-- 同じ関数を適用しても、同じ。
cong : forall {A B : Set} (f : A -> B) {x y} -> x ≡ y -> f x ≡ f y
cong f refl = refl

{--
  整数による cong のテスト
  --}
data ℕ : Set where
  zero : ℕ
  suc : ℕ -> ℕ

infixr 40 _+_
_+_ : ℕ -> ℕ -> ℕ
n + zero   = n
n + suc m = suc (n + m)

foo : (n : ℕ) -> n + zero ≡ n
foo zero = refl
foo (suc m) = cong suc (foo m)

{--
  リストによる ≡ と rev のテスト
  --}
infixr 30 _::_
data List (A : Set) : Set where
   []    : List A
   _::_  : A -> List A -> List A

-- Append
infixr 20 _++_
_++_ : {A : Set} -> List A -> List A -> List A
[]     ++ l' = l'
a :: l ++ l' = a :: (l ++ l')

-- Reverse
rev : {A : Set} -> List A -> List A
rev [] = []
rev (a :: l) = (rev l) ++ (a :: [])

-- cong_rev_list : {x y : List ℕ} -> x ≡ y -> rev x ≡ rev y
-- cong_rev_list refl = refl

example : List ℕ
example = zero :: (suc zero) :: (suc (suc zero)) :: []

test-reverse : rev (rev example) ≡ example
test-reverse = refl

test-reverse1 : example ≡ rev (rev example)
test-reverse1 = refl

test-reverse2 : rev example ≡ rev example
test-reverse2 = refl

-- test-reverse_ng : rev example ≡ example
-- test-reverse_ng = ?                         -- No solution found

test-reverse0 : rev (zero :: []) ≡ zero :: []
test-reverse0 = refl

lemma_cong_rev2 : {A : Set} -> {x y : List A} -> x ≡ y -> rev x ≡ rev y
lemma_cong_rev2 refl = refl

lemma_cong_rev : {A : Set} -> {x : List A} -> rev x ≡ rev x
lemma_cong_rev = refl

-- lemma_rev_rev : {A : Set} -> (x : List A) -> rev (rev x) ≡ x
-- lemma_rev_rev [] = refl
-- lemma_rev_rev (zero :: zero :: []) = refl

-- END
