{-
  F-algebra と Maybe
  @suharahiromichi
  
  F-algebra と catamorphism を Haskell で理解する(1)(2)
  http://d.hatena.ne.jp/itto100pen/20090605/1244206128
  http://d.hatena.ne.jp/itto100pen/20090607#1244400811
  
  ループ書いたら負けかなと思っている
  http://www.wankuma.com/seminar/20090704osaka30/4.pdf  

  http://ja.wikipedia.org/wiki/F代数
  http://ja.wikipedia.org/wiki/始代数
  http://ja.wikipedia.org/wiki/Catamorphism
-}

module agda_maybe_falgebra where

open import Data.Nat
open import Data.Bool
open import Data.List
open import Function                        -- id

{-
F代数
圈C自己関手Fが定義されていているとき、
圈Cの対象Aと、圈Cの射a:FA->Aの組、(A,a)を関手FのF代数と呼ぶ。
（もっと簡単に、「aは代数」という場合もあるようだ。）

凖同型射
任意の対象Bと、任意の射b:FB->B、に対して、
図が可換であるとき、射f:A->BをF代数(A,a)から(B,b)への凖同型射という。
F代数と凖同型射の全体は、圈をなす。

F始代数
F代数と凖同型射からなる圈が始対象aを持つとき、F始代数である。
自己関手は、Xを1+Xに対応づけることになる。

Catamorphism
以上を満たすとき、fは一意に決まるので、bの高階関数(|b|)で表し、
Catamorphism または バナナ と呼ぶ。
（本来は射を指すのだが、高階演算子(|_|)をいう場合もあるようだ。）

.         a 始対象
  FA------------------------>A
  |                          |
  |                          |
  | F(f)                     | f = (|b|)
  |                          |  Catamorphism
  v                          v
  FB------------------------>B
  .        b 任意の射
-}

{-
Maybe Nの例
(1) 自己関手(型関手)Fを、Maybeとする。
(2) 自然数の集合Nと、関数Z:1->N、S:N->NはF始代数である。
    対象Aは、N
    始対象の射は、[Z,S]
(3) 対象Bも、N （とりあえず）
    F(f)は、fmap fとする。

問題
  任意のbに対して、fを求める。

.            [Z,S]
Maybe N--------------------->N
  |                          |
  |                          |
  | fmap f                   | f = (|b|)
  |                          | を求める。
  v                          v
Maybe N--------------------->N
  .           b から、、、
-}

data Maybe {a} (A : Set a) : Set a where
  nothing : Maybe A
  some : (x : A) -> Maybe A

Z : Maybe ℕ -> ℕ
Z _ = zero

S : Maybe ℕ -> ℕ
S nothing = zero
S (some n) = suc n

fmap : {a b : Set} -> (a -> b) -> Maybe a -> Maybe b
fmap _ nothing = nothing
fmap f (some x) = some (f x)

-- bが、[Z,S]のとき。
b1 : Maybe ℕ -> ℕ
b1 nothing = zero
b1 (some x) = suc x

-- bが、[1, 2*x]のとき。
b2 : Maybe ℕ -> ℕ
b2 nothing = suc zero
b2 (some x) = 2 * x

rec : (Maybe ℕ -> ℕ) -> ℕ -> ℕ
rec b zero = b nothing
rec b (suc n) = (b (some (rec b n)))

-------------
-- 検算
-- equality
data _≡_ {A : Set} (x : A) : A -> Set where
  refl : x ≡ x

-- Id
-- rec b1 n ≡ n
l1 : rec b1 (suc (suc zero)) ≡ suc (suc zero)
l1 = refl

-- rec b2 n ≡ 2^n
l2 : rec b2 (suc (suc zero)) ≡ (suc (suc (suc (suc zero))))
l2 = refl

-------------
-- 証明
-- 未了。

-- END
