{-
  Dependently Typed Programming in Agda
  Ulf Norell

  2.5 Programs as proofs
  2.6 More on pattern matching
-}

module agda_ulfn25 where

module AgdaBasics where

data Bool : Set where
  true : Bool
  false : Bool

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat

infixl 40 _+_
_+_ : Nat -> Nat -> Nat
zero + m = m
suc n + m = suc (n + m)

infixr 40 _::_
data List (A : Set) : Set where
  [] : List A
  _::_ : A -> List A -> List A

-- 2.5 Programs as proofs
data False : Set where                      -- 要素はない（空）
record True : Set where                     -- 要素はひとつだけ

trivial : True
trivial = _

isTrue : Bool -> Set
isTrue true = True
isTrue false = False

_<_ : Nat -> Nat -> Bool
_ < zero = false
zero < suc n = true
suc m < suc n = m < n

length : {A : Set} -> List A -> Nat
length [] = zero
length (x :: xs) = suc (length xs)

lookup : {A : Set}(xs : List A)(n : Nat) ->
  isTrue (n < length xs) -> A
lookup [] n ()
lookup (x :: xs) zero p = x
lookup (x :: xs) (suc n) p = lookup xs n p

data _==_ {A : Set}(x : A) : A -> Set where
  refl : x == x

data _≤_ : Nat -> Nat -> Set where          -- \le
  leq-zero : {n : Nat} -> zero ≤ n
  leq-suc : {m n : Nat} -> m ≤ n -> suc m ≤ suc n

leq-trans : {l m n : Nat} -> l ≤ m -> m ≤ n -> l ≤ n
leq-trans leq-zero _ = leq-zero
leq-trans (leq-suc p) (leq-suc q) = leq-suc (leq-trans p q)

-- 2.6 More on pattern matching
min : Nat -> Nat -> Nat
min x y with x < y
min x y | true = x
min x y | false = y
--- 実際の引数 | with値　= 定義

filter : {A : Set} -> (A -> Bool) -> List A -> List A
filter p [] = []
filter p (x :: xs) with p x
... | true = x :: filter p xs
... | false = filter p xs
--- 実際の引数 は、「...」と省略してもよい。
--- しなくて、パターンマッチを併用してもよい。

data _≠_ : Nat -> Nat -> Set where  -- \ne
  z≠s : {n : Nat} -> zero ≠ suc n  -- 「n≠s」はコンストラクタの名前
  s≠z : {n : Nat} -> suc n ≠ zero
  s≠s : {m n : Nat} -> m ≠ n -> suc m ≠ suc n

data Equal? (n m : Nat) : Set where
  eq : n == m -> Equal? n m
  neq : n ≠ m -> Equal? n m

equal? : (n m : Nat) -> Equal? n m
equal? zero zero = eq refl
equal? zero (suc m) = neq z≠s
equal? (suc n) zero = neq s≠z
equal? (suc n) (suc m) with equal? n m
equal? (suc n) (suc .n) | eq refl = eq refl -- dot notation
equal? (suc n) (suc m) | neq p = neq (s≠s p)

infix 20 _⊆_                               -- \sub=
data _⊆_ {A : Set} : List A -> List A -> Set where
  stop : [] ⊆ []
  drop : forall {xs y ys} -> xs ⊆ ys -> xs ⊆ y :: ys
  keep : forall {x xs ys} -> xs ⊆ ys -> x :: xs ⊆ x :: ys

lem-filter : {A : Set}(p : A -> Bool)(xs : List A) -> filter p xs ⊆ xs
lem-filter p [] = stop
lem-filter p (x :: xs) with p x
... | true  = keep {x = x} (lem-filter p xs) -- 関数定義の{}は省略できる。
... | false = drop {y = x} (lem-filter p xs) -- 関数定義の{}は省略できる。

{-
Let us walk through it slowly:
  lem-filter p (x :: xs) = ?
At this point the goal that we have to prove is
  (filter p (x :: xs) | p x) ⊆　x :: xs

In the goal filter has been applied to its with abstracted argument p x
and will not reduce any further. Now, when we abstract over p x it will
be abstracted from the goal type so we get
  lem-filter p (x :: xs) with p x
    ... | px = ?

where p x has been replaced by px in the goal type
  (filter p (x :: xs) | px) ⊆ x :: xs

Now, when we pattern match on px the call to filter will reduce and we get
  lem-filter p (x :: xs) with p x
    ... | true = ? {- x :: filter p xs ⊆ x :: xs -}
    ... | false = ? {- filter p xs ⊆ x :: xs -}
-}

-- 関数の引数パターンに{}を書く例、この場合は定義右辺でyを使うので省略できない。
complement_list : {A : Set} {xs ys : List A} -> xs ⊆ ys -> List A
complement_list stop             = []
complement_list (drop {y = y} p) = y :: (complement_list p) -- {}は省略できない。
complement_list (keep p)         = (complement_list p)

lem-plus-zero : (n : Nat) -> n + zero == n
lem-plus-zero zero = refl
lem-plus-zero (suc n) with n + zero | lem-plus-zero n
lem-plus-zero (suc n)    | .n       | refl            = refl -- dot notation
-- with値は複数もつことができる、
-- n+zeroとn
-- lem-plus-zero nとrefl

{-
ラシウラさんの説明から。
「.」つきの識別子はパターン中で使うもので、with行のドットなしのものと同
じものであることを示すもののようです。ドットなしだと名前は同じでもあら
たな別の変数として解釈されるようです。
-}

{-
In the step case we would like to pattern match on the 
induction hypothesis n + zero == n in order to prove suc n + zero == suc n,
帰納法の仮説　n + zero == n から　suc n + zero == suc n を導く。

but since n + zero cannot be uniﬁed with n that is not allowed. 
しかし、n + zero は n とユニファイしないので、

However, if we abstract over n + zero, calling it m, 
n + zero を m とする。

we are left with the induction hypothesis m == n and the goal suc m == suc n. 
帰納法の仮説 m == n とおいて、suc m = suc n をゴールとする。

Now we can pattern match on the induction hypothesis, instantiating m to n.
m を n にパターンマッチすることはできる。
-}

-- Exercise 2.3. Sublists
-- Remember the representation of sublists from Section 2.4:
-- (a)
-- Prove the reﬂexivity and transitivity of ⊆ :

⊆-refl : {A : Set} {xs : List A} -> xs ⊆ xs
⊆-refl {_} {[]} = stop
⊆-refl {_} {x :: xs} = keep ⊆-refl

⊆-trans : {A : Set} {xs ys zs : List A} -> xs ⊆ ys -> ys ⊆ zs -> xs ⊆ zs
⊆-trans stop     stop = stop
⊆-trans stop     (drop q) = drop q
⊆-trans (drop p) (keep q) = drop (⊆-trans p q)
⊆-trans (keep p) (keep q) = keep (⊆-trans p q)
⊆-trans p        (drop q) = drop (⊆-trans p q)

-- infixr 30 _::_
data SubList {A : Set} : List A -> Set where
  [] : SubList []
  _::_ : forall x {xs} -> SubList xs -> SubList (x :: xs)
  skip : forall {x xs} -> SubList xs -> SubList (x :: xs)

test_list : List Nat
test_list = zero :: suc zero :: suc (suc zero) :: suc (suc (suc zero)) :: []

test_sublist1 : SubList test_list
test_sublist1 = zero :: suc zero :: suc (suc zero) :: suc (suc (suc zero)) :: []

-- (b) Deﬁne a function to extract the list corresponding to a sublist.

forget : {A : Set} {xs : List A} -> SubList xs -> List A
forget [] = []
forget (x :: xs) = x :: (forget xs)
forget (skip xs) = forget xs

-- (c) Now, prove that a SubList is a sublist in the sense of ⊆ .

lem-forget : {A : Set}{xs : List A}(zs : SubList xs) -> (forget zs) ⊆ xs
lem-forget [] = stop
lem-forget (z :: zs)     = keep {x = z} (lem-forget zs) -- {}は省略できる。
lem-forget (skip {x} zs) = drop {y = x} (lem-forget zs) -- どちらの{}も省略できる。

-- (d) Give an alternative deﬁnition of ﬁlter which satisﬁes the
-- sublist property by construction.

filter' : {A : Set} -> (A -> Bool) -> (xs : List A) -> SubList xs
filter' p [] = []
filter' p (x :: xs) = x :: filter' p xs

-- (e) Deﬁne the complement of a sublist (補集合)

complement : {A : Set} {xs : List A} -> SubList xs -> SubList xs
complement [] = []
complement (z :: zs) = skip (complement zs)
complement (skip {x} zs) = x :: (complement zs) -- {}は省略できる。

-- (f) Compute all sublists of a given list

--sublists : {A : Set} (xs : List A) -> List (SubList xs)
sublists : {A : Set} (xs : List A) -> (SubList xs)
-- sublists [] = [] :: []
sublists [] = []
sublists (x :: xs) = {!!}

-- END
