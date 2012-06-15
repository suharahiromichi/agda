{-
  Dependently Typed Programming in Agda
  Ulf Norell

  2.3 Implicit arguments
  に Warning: the following type is not for the faint of heart!
  と書かれた、関数合成(dot op) ∘ を理解する。
-}

module agda_ulfn23 where

module AgdaBasics where

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat

data Bool : Set where
  true : Bool
  false : Bool

infixr 40 _::_
data List (A : Set) : Set where
  [] : List A
  _::_ : A -> List A -> List A

identity : (A : Set) -> A -> A
identity A x = x

id : {A : Set} -> A -> A
id x = x                                    -- identity

true’ : Bool
true’ = id true

silly : {A : Set} {x : A} -> A              -- silly : {A : Set} -> {x : A} -> A でもおなじ。
silly {_} {x} = x

false’ : Bool
false’ = silly {x = false}
{-
there is no way the type checker could ﬁgure out what the second
argument to silly should be. To provide an implicit argument
explicitly you use the implicit application syntax f {v}, which gives
v as the left-most implicit argument to f, or as shown in the example
above, f {x = v}, which gives v as the implicit argument called x. The
name of an implicit argument is obtained from the type declaration.
-}

one : Nat
one = identity _ (suc zero)

-- チュートリアルにある、もともとの定義
-- ∘ は \o
-- (Warning: the following type is not for the faint of heart!)
_∘_ : {A : Set}{B : A -> Set}{C : (x : A) -> B x -> Set}
      (f : {x : A}(y : B x) -> C x y) ->
      (g : (x : A) -> B x) ->
      (x : A) ->
    C x (g x)
(f ∘ g) x = f (g x)                      -- f g x の名前は任意でよい。

plus-two : Nat -> Nat                       -- 書かなくてもよい。
plus-two = suc ∘ suc

{-
  納得できるまで、型の記述を単純にしてみる。
-}

-- Nat->Nat型の関数に制限する場合
-- Nat->Nat->Nat
_dot0_ :
       (f : Nat -> Nat) ->
       (g : Nat -> Nat) ->
       (x : Nat) -> Nat
-- f:、g:、x:はなくてもよい。以下同様。
-- _dot0_ : (Nat -> Nat) -> (Nat -> Nat) -> Nat -> Nat
(f dot0 g) x = f (g x)                   -- f g x の名前は任意でよい。
plus-two0 = suc dot0 suc

-- 任意の型（ただし、すべておなじ）に制限する場合
-- Aの定義だけ有効にした場合。A->A->A
_dot1_ : {A : Set}
       (f : A -> A) ->
       (g : A -> A) ->
       (x : A) -> A
-- {A:Set} -> と -> をいれてもよい。
-- また、最後の -> 以外は省略できるようだ。
(f dot1 g) x = f (g x)                   -- f g x の名前は任意でよい。
plus-two1 = suc dot1 suc

-- 途中(gの戻りとfの引数)は任意の同じ型とする場合
-- Bの定義だけ有効にした場合。Nat->B->Nat
_dot2_ : {B : Nat -> Set}
       (f : {x : Nat} -> (y : B x) -> Nat)
       (g : (x : Nat) -> B x)
       (x : Nat) -> Nat
(f dot2 g) x = f (g x)                    -- f g x の名前は任意でよい。
plus-two2 = suc dot2 suc

-- 途中はかならずNat型とする場合
-- AとCの定義だけ有効にした場合。A->Nat->C
_dot3_ : {A : Set}{C : (x : A) -> Nat -> Set}
       (f : {x : A}(y : Nat) -> C x y)
       (g : (x : A) -> Nat)
       (x : A) -> C x (g x)
(f dot3 g) x = f (g x)                    -- f g x の名前は任意でよい。
plus-two3 = suc dot3 suc

-- BとCの定義だけ有効にした場合。Nat->B->C
_dot4_ : {B : Nat -> Set}{C : (x : Nat) -> B x -> Set}
       (f : {x : Nat} -> (y : B x) -> C x y)
       (g : (x : Nat) -> B x)
       (x : Nat) -> C x (g x)
(f dot4 g) x = f (g x)                    -- f g x の名前は任意でよい。
plus-two4 = suc dot4 suc

-- AとBの定義だけ有効にした場合。A->B->Nat
-- ??

-- Cの定義だけ有効にした場合。Nat->Nat->C
_dot6_ : {C : (x : Nat) -> Nat -> Set}
       (f : {x : Nat}(y : Nat) -> C x y)
       (g : (x : Nat) -> Nat)
       (x : Nat) -> C x (g x)
(f dot6 g) x = f (g x)                    -- f g x の名前は任意でよい。
plus-two6 = suc dot6 suc
  
-- 応用のためのコード
map : {A B : Set} -> (A -> B) -> List A -> List B
map f [] = []
map f (x :: xs) = f x :: map f xs

_++_ : {A : Set} -> List A -> List A -> List A
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

--- テストコード
test23 : List Nat                           -- 書かなくてよい。
test23 = zero :: suc zero :: suc (suc zero) :: []

-- equality
data _≡_ {A : Set} (x : A) : A -> Set where
  refl : x ≡ x

test23-1 : map suc (map suc test23) ≡ map plus-two test23
test23-1 = refl

-- END
