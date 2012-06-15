{-
  Dependent Types at Work
  Ana Bove and Peter Dybjer

  4. Propositions as Types 後半部分
-}

module agda_atwork43_godel_t where

open import Data.Nat
open import Data.Bool

-- 4.3 Equality
infix 6 _==_
data _==_ {A : Set} : A -> A -> Set where
  refl : (a : A) -> a == a

subst : {A : Set} -> {C : A -> Set} -> (a’ a’’ : A) ->
  a’ == a’’ -> C a’ -> C a’’
subst .a .a (refl a) c = c

-- 4.4 Induction Principles

{-
Data.Bool で、定義済み。
if_then_else_ : {C : Set} -> Bool -> C -> C -> C
if true then x else y = x
if false then x else y = y
-}

natrec : {C : ℕ -> Set} -> (C zero) ->
       ((m : ℕ) -> C m -> C (suc m)) -> (n : ℕ) -> C n
natrec p h zero = p
natrec p h (suc n) = h n (natrec p h n)

plus : ℕ -> ℕ -> ℕ
plus n m = natrec m (\x y -> suc y) n

mult : ℕ -> ℕ -> ℕ
mult n m = natrec zero (\x y -> plus y m) n

eq-suc : {n m : ℕ} -> n == m -> suc n == suc m
eq-suc (refl n) = refl (suc n)

eq-plus-rec : (n m : ℕ) -> n + m == plus n m
eq-plus-rec n m = natrec (refl m) (\k’ ih -> eq-suc ih) n

eq-mult-rec : (n m : ℕ) -> n + m == mult n m
eq-mutl-rec n m = ?

eq-plus : (n m : ℕ) -> n + m == plus n m
eq-plus zero m = refl m
eq-plus (suc n) m = eq-suc (eq-plus n m) -- suc (n + m) == suc (natrec m (λ x → suc) n)

eq-suc-k : {n m : ℕ} {C : ℕ -> ℕ} -> (k : ℕ) -> n == m -> k + n == plus k m
eq-suc-k zero (refl n) = refl n
eq-suc-k (suc k) (refl n) = eq-suc (eq-suc-k k (refl n))

eq-mult : (n m : ℕ) -> n * m == mult n m
eq-mult zero m = refl zero
eq-mult (suc n) m = {!!}
-- eq-suc-k m (eq-mult n m)
-- (m + n * m) == natrec m (λ x → suc) (natrec 0 (λ x y → natrec m (λ x' → suc) y) n)
---     ~~~~~                           ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
---     n * m                           mult n m

-- END
