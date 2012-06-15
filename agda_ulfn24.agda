{-
  Dependently Typed Programming in Agda
  Ulf Norell

  2.4 Datatype families
  dot表記について。
  Fin nデータ型について。
-}

module agda_ulfn24 where

module AgdaBasics where

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat

infixr 40 _::_
data List (A : Set) : Set where
  [] : List A
  _::_ : A -> List A -> List A

-- \o
_∘_ : {A : Set}{B : A -> Set}{C : (x : A) -> B x -> Set}
    (f : {x : A}(y : B x) -> C x y)
    (g : (x : A) -> B x)
    (x : A) -> C x (g x)
(f ∘ g) x = f (g x)                      -- f g x の名前は任意でよい。

-- 2.4 Datatype families
data Vec (A : Set) : Nat -> Set where
  [] : Vec A zero
  _::_ : {n : Nat} -> A -> Vec A n -> Vec A (suc n)

head : {A : Set}{n : Nat} -> Vec A (suc n) -> A
head (x :: xs) = x

vmap : {A B : Set}{n : Nat} -> (A -> B) -> Vec A n -> Vec B n
vmap f [] = []
vmap f (x :: xs) = f x :: vmap f xs

-- Dot patterns
{-
For instance, what happens　with the length argument when we pattern match on the list?
To see this, let us deﬁne new versions of Vec and vmap with fewer implicit arguments:

長さ引数が、リストとマッチしたらなにが起きるか？
それを見るために、長さ引数{n : Nat}を Vec(::)から、vmap に移した。
-}

data Vec2 (A : Set) : Nat -> Set where
  nil : Vec2 A zero
  cons : (n : Nat) -> A -> Vec2 A n -> Vec2 A (suc n)

vmap2 : {A B : Set}(n : Nat) -> (A -> B) -> Vec2 A n -> Vec2 B n
vmap2 .zero f nil = nil
vmap2 .(suc n) f (cons n x xs) = cons n (f x) (vmap2 n f xs)

{-
if the list turns out to be nil then the length argument must be zero,
and if the list is cons n x xs then the only type correct value for
the length argument is suc n
もし、リストがnilと判明した場合、長さの引数は0でなければならず、また、
リストがcons n x xsなら、長さ引数はsuc nでなければならない。

To indicate that the value of an argument has been deduced by type checking,
rather than observed by pattern matching it is preﬁxed by a dot (.).
引数の値が、明らかなマッチングではなく、タイプチェッキングによって推定されることを示すために、
dot (.) をプリフィックスにおく。
-}

vmap3 : {A B : Set}(n : Nat) -> (A -> B) -> Vec2 A n -> Vec2 B n
vmap3 zero f nil = nil
vmap3 (suc n) f (cons .n x xs) = cons n (f x) (vmap3 n f xs)

data Image_∋_ {A B : Set}(f : A -> B) : B -> Set where -- \ni
  im : (x : A) -> Image f ∋ f x

inv : {A B : Set}(f : A -> B)(y : B) -> Image f ∋ y -> A
inv f .(f x) (im x) = x

-- Absurd patterns
-- numbers smaller than a given natural number.
-- 与えられた自然数より小さな数字のファミリ
data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc : {n : Nat} -> (i : Fin n) -> Fin (suc n)
{-
  Here fzero is smaller than suc n for any n
  任意のnについて、fzeroはsuc nより小さい
  and if i is smaller than n then fsuc i is smaller than suc n.
  iがnより小さいなら、fsuc iは、suc nより小さい。
  (fsuc の i: は省略可能だが、説明とあわせるためにつけた。)
  
  Note that there is no way of constructing a number smaller than zero. 
  zeroより小さな数字を構成する方法はない。
-}

{-
When there are no possible constructor patterns for a given argument
you can pattern match on it with the absurd pattern ():
与えられた引数にたいして、可能なコンストラクタパタンがない場合は、
それにたいして、パターン「()」をマッチさせることができる。
-}
magic : {A : Set} -> Fin zero -> A
magic ()

data Empty : Set where
  empty : Fin zero -> Empty

magic' : {A : Set} -> Empty -> A
magic' (empty ())
-- magic' () -- not accepted

{-
Given a list of length n and a number i smaller than n
we can compute the ith element of the list (starting from 0)
与えられたリストの長さがnで、数iがnより小さいなら、i番めの要素を得ることができる。
-}

_!_ : {n : Nat}{A : Set} -> Vec A n -> Fin n -> A
[] ! ()                                     -- 空リスト
(x :: xs) ! fzero = x                       -- 先頭の要素
(x :: xs) ! (fsuc i) = xs ! i               -- それ以外の要素

-- テストコード
test : Vec Nat (suc (suc (suc zero)))
test = zero :: zero :: zero :: []

test0 = test ! fzero
test1 = test ! (fsuc fzero)
test2 = test ! (fsuc (fsuc fzero))
-- test3 = test ! (fsuc (fsuc (fsuc fzero)))
{-
The types ensure that there is no danger of indexing outside the list.
This is reﬂected in the case of the empty list where there are no possible
values for the index.
-}

{-
The _!_ function turns a list into a function from indices to elements.
!関数は、リストから要素を返す。

constructing a list given a function from indices to elements:
与えられた（インデックスから要素への）関数からリストを構成する：
-}

tabulate : {n : Nat}{A : Set} -> (Fin n -> A) -> Vec A n
tabulate {zero} f = []
tabulate {suc n} f = f fzero :: tabulate (f ∘ fsuc)

{-
Note that tabulate is deﬁned by recursion over the length of the
result list, even though it is an implicit argument. There is in general
no correspondance between implicit data and computationally irrelevant
data
-}

-- テストコード
-- Fin nをNatに変換する関数
tabulate_f : {n : Nat} -> Fin n -> Nat
tabulate_f fzero = zero
tabulate_f (fsuc n) = suc (tabulate_f n)

-- [0,1,2]
tabulate_test' : Vec Nat (suc (suc (suc zero)))
tabulate_test' = zero :: (suc zero) :: (suc (suc zero)) :: []

-- Vec Nat 3 の型を埋める、Natを求める。
tabulate_test : Vec Nat (suc (suc (suc zero)))
tabulate_test = tabulate tabulate_f

-- equality
data _≡_ {A : Set} (x : A) : A -> Set where
  refl : x ≡ x

tabulate_test_result : tabulate_test ≡ tabulate_test'
tabulate_test_result = refl

-- 2.9 Exercises
-- Exercises 2.1. Matrix transposition
Matrix : Set -> Nat -> Nat -> Set
Matrix A n m = Vec (Vec A n) m

-- (a)
-- Define a function to compute a vector containing n copies of an element x
vec : {n : Nat}{A : Set} -> A -> Vec A n
vec {zero} x = []
vec {suc n} x = x :: vec {n} x

testex21a : vec {suc (suc (suc zero))} zero ≡ zero :: zero :: zero :: []
testex21a = refl

-- (b)
-- Define point-wise application of a vector of functions to a vector of arguments.
infixl 90 _$_
_$_ : {n : Nat}{A B : Set} -> Vec (A -> B) n -> Vec A n -> Vec B n
[] $ [] = []
(f :: fs) $ (x :: xs) = f x :: fs $ xs

xs : Vec Nat (suc (suc (suc zero)))
xs = zero :: (suc zero) :: (suc zero) :: []
fs : Vec (Nat -> Nat) (suc (suc (suc zero)))
fs = suc :: suc :: suc :: []
testex21b : fs $ xs ≡ vmap suc xs
testex21b = refl

-- (c)
-- Deﬁne matrix transposition in terms of these two functions.

tail : {A : Set}{n : Nat} -> Vec A (suc n) -> Vec A n
tail (_ :: xs) = xs

transpose1 : forall {A n m} -> Vec (Vec A (suc n)) (suc m) -> Vec A (suc m)
transpose1 xss = vmap head xss

transpose2 : forall {A n m} -> Matrix A (suc n) (suc m) -> Vec A (suc m)
transpose2 xss = vmap head xss

transpose3 : forall {A n m} -> Vec (Vec A (suc n)) (suc m) -> Vec (Vec A n) (suc m)
transpose3 xss = vmap tail xss

transpose4 : forall {A n m} -> Matrix A (suc n) (suc m) -> Matrix A n (suc m)
transpose4 xss = vmap tail xss

test_z00 : Vec (Vec Nat zero) zero
test_z00 = []
test_z11 : Vec (Vec Nat (suc zero)) (suc zero)
test_z11 = (zero :: []) :: []
test_z10 : Vec (Vec Nat (suc zero)) zero
test_z10 = []                               -- vec (vec zero) としてもよい。
test_z01 : Vec (Vec Nat zero) (suc zero)
test_z01 = vec (vec zero)            -- 適当に要素を詰め込んでくれる。

transpose : forall {A n m} -> Matrix A n m -> Matrix A m n
-- transpose : {A : Set} {n : Nat} {m : Nat} -> Matrix A n m -> Matrix A m n
transpose {A} {zero} {zero} [] = []
transpose {A} {zero} {suc m} _ = []         -- ひとつ上とまとめてもよい。
transpose {A} {suc n} {zero} _ = vec []
transpose {A} {suc n} {suc m} xss = vmap head xss :: transpose (vmap tail xss)
-- 右辺の transpose には　{A} {n} {(suc m)} が与えられる、が書かなくてよい。

-- http://d.hatena.ne.jp/yoriyuki/20080627
-- vec [] というのは気がつかなかった。n行0列を作る手段はこれしかないわけだ。
-- 参考にしたyoriyukiさんのコードでは、第3式の右辺は以下になっている。
-- (vec head) $ xss :: transpose (vec tal $ xss)

-- Exercise 2.2. Vector lookup
-- (a)
-- This direction should be relatively easy.

lem-!-tab : forall {A n} (f : Fin n -> A)(i : Fin n) ->
  ((tabulate f) ! i) ≡ f i
lem-!-tab f fzero = refl
lem-!-tab f (fsuc n) = lem-!-tab (\ z → f (fsuc z)) n
-- lem-!-tab f fzero = { }0
-- lem-!-tab f (fsuc n) = { }1
-- のそれぞれに対して、C-c C-a で自動的に解けてしまう。

-- (b)
-- This direction might be trickier.

-- 同じ関数を適用しても、同じ。
cong : forall {A B : Set} {x y : A} (f : A -> B) -> x ≡ y -> f x ≡ f y
cong f refl = refl

-- 停止判定がされない。
-- cong_vec : {A : Set} {n : Nat} {x : A} {y z : Vec A n} -> y == z -> x :: y == x :: z
-- cong_vec refl = refl

lem-tab-! : forall {A n} (xs : Vec A n) -> tabulate (_!_ xs) ≡ xs
-- (_!_ xs) は (λ x' → xs ! x') と同じこと。
lem-tab-! {A} {zero} [] = refl
lem-tab-! {A} {suc n} (x :: xs) = cong (λ y -> x :: y) (lem-tab-! {A} {n} xs)
--        tabulate (λ x' → xs ! x') == xs
--------------------------------------------------- cong (λ y -> x :: y)
-- (x :: tabulate (λ x' → xs ! x')) == (x :: xs)

-- END
