module agda_list where

infixr 30 _::_
data List (A : Set) : Set where
   []    : List A
   _::_  : A -> List A -> List A

data Nat : Set where
  Z : Nat
  S : Nat -> Nat

infixr 40 _+_
_+_ : Nat -> Nat -> Nat
n + Z   = n
n + S m = S (n + m)

length : {A : Set} -> List A -> Nat
length []       = Z
length (_ :: l) = S (length l)

sumlist : List Nat -> Nat
sumlist [] = Z
sumlist (n :: l)  = n + sumlist l

-- Append
infixr 20 _++_
_++_ : {A : Set} -> List A -> List A -> List A
[]     ++ l' = l'
a :: l ++ l' = a :: (l ++ l')

-- Reverse
rev : {A : Set} -> List A -> List A
rev [] = []
rev (a :: l) = (rev l) ++ (a :: [])

test_rev : List Nat
test_rev = rev (Z :: (S Z) :: (S (S Z)) :: [])

-- Map
map : {A : Set} -> (A -> A) -> List A -> List A
map f []        = []
map f (n :: l') = f n :: map f l'

test_map : List Nat
test_map = map S (Z :: (S Z) :: (S (S Z)) :: [])

-- at
-- at : {A : Set} -> (n : Nat) -> (l : List A) -> A
-- at n [] ()
-- at Z (e :: []) = e
-- at (S n) (_ :: l) = at n l
-- Dependently Typed Programming in Agda, Ulf Norell
-- 2.4 Datatype families および、
-- 2.5 Programs as proofs を参照のこと。

-- END
