module agda_ulfn31_views_parity where

{-
  Dependently Typed Programming in Agda
  Ulf Norell
  3.1 Views
  3.3 Exercises 3.1. Natural numbers
-}

open import Data.Nat

-- Natural number parity

data Parity : ℕ -> Set where
  even : (k : ℕ) -> Parity (k * 2)
  odd  : (k : ℕ) -> Parity (1 + k * 2)

parity : (n : ℕ) -> Parity n
parity zero = even zero
parity (suc n)         with parity n
parity (suc .(k * 2))     | even k   = odd k
parity (suc .(1 + k * 2)) | odd k    = even (suc k)

half : ℕ -> ℕ
half n         with parity n
half .(k * 2)     | even k   = k
half .(1 + k * 2) | odd k    = k

-- Exercise 3.1. Natural numbers

data Compare : ℕ -> ℕ -> Set where           
  less : forall {n} k -> Compare n (n + suc k)
  more : forall {n} k -> Compare (n + suc k) n
  same : forall {n}   -> Compare n n               

-- (a) Deﬁne the view function

comp : (n m : ℕ) -> Compare n m
comp zero zero = same
comp zero (suc k) = less k
comp (suc k) zero = more k
comp (suc n) (suc m)         with comp n m
comp (suc n) (suc .(n + suc k)) | less k = less k
comp (suc .(n + suc k)) (suc n) | more k = more k
comp (suc .n) (suc n)           | same   = same -- dotは二つのnのうちのどちらか。

-- (b) Now use the view to compute the diﬀerence between two numbers

difference : ℕ -> ℕ -> ℕ
difference n m         with comp n m
difference n .(n + suc k) | less k = k
difference .(n + suc k) n | more k = k
difference .n n           | same   = zero

-- END
