{-
  Record のサンプル
  agda_stdlib の Category.Monad モナドの使い方
  2012_06_09
-}

module agda_rec_sample where

open import Data.Nat
open import Data.Bool
open import Data.List
open import Function                        -- id

-- Leibnitz equality
data _≡_ {A : Set} (x : A) : A -> Set where
  refl : x ≡ x

-------------------------------------------------------
-- 「Agda言語について」の例
-- http://ocvs.cfv.jp/tr-data/PS2008-014.pdf
-- 
record BN : Set where
  field
    f1 : ℕ
    f2 : Bool

aBN : BN
aBN = record {f1 = 1; f2 = true}
-- aBN : BN
-- BN.f1 : BN -> ℕ    なる関数が自動で定義される。
-- BN.f2 : BN -> Bool なる関数が自動で定義される。
a : ℕ
a = BN.f1 aBN                               -- aBN.f1 ではだめ。

--------------------------------------
-- 依存型レコード

data Array (A : Set) : ℕ -> Set where
  [] : Array A zero
  _::_ : {n : ℕ} -> A -> Array A n -> Array A (suc n)

record VR : Set where
  field
    len : ℕ
    arr : Array Bool len

aVR : VR
aVR = record {len = suc zero ; arr = true :: []}

alen : ℕ
alen = VR.len aVR

adat1 : Array Bool (suc zero)
adat1 = VR.arr aVR

--------------------------------------
-- パラメータ付きレコード

record PVR (X : Set) : Set where
  field
    len' : ℕ
    arr' : Array X len'

aPVR : PVR ℕ
aPVR = record {len' = zero ; arr' = []}

alen' : ℕ
alen' = PVR.len' aPVR

-------------------------------------------------------
-- 参考論文の 4.論理の符号化の例
--

record _&&_ (P Q : Set) : Set where
  field
    Elim1 : P
    Elim2 : Q

and-intro : {P Q : Set} -> P -> Q -> P && Q
and-intro a b = record { Elim1 = a ; Elim2 = b }

-- 参考論文では、&&.Elim1 のように「_」を省略できそうだが、間違いのようだ。
-- _&&_.Elim1 : {P Q : Set} -> P ∧ Q -> P
-- _&&_.Elim2 : {P Q : Set} -> P ∧ Q -> Q

lemma : {A B : Set} -> (A && B) -> (B && A)
lemma {a} {b} p = and-intro (_&&_.Elim2 p) (_&&_.Elim1 p)


-------------------------------------------------------
-- Monad
-- agda_stdlib をつかう。
--
open import Category.Monad
-- 実際の定義 : Category/Monad/Indexed

list-monad : ∀ {ℓ} -> RawMonad (List {ℓ})
list-monad = record {
    return = λ x -> x ∷ [];
    _>>=_  = λ xs f -> concat (map f xs)   -- bind
    }

-- returnを直接使ってみる。
return' : ∀ {A} -> A -> List A
return' = RawMonad.return list-monad

test1' : List ℕ
test1' = return' zero

lem1' : {n : ℕ} -> (return' n) ≡ (n ∷ [])  -- list Nat
lem1' = refl

-- bindを直接使ってみる。
infixr 1 _>>='_
_>>='_  : ∀ {A} {B} -> List A -> (A -> List B) -> List B
_>>='_  = RawMonad._>>=_ list-monad

test2' : List ℕ
test2' = (zero ∷ []) >>=' (\x -> x ∷ [])

lem2' : {n : ℕ} -> ((n ∷ []) >>=' (\x -> x ∷ [])) ≡ (n ∷ [])  -- list Nat
lem2' = refl

----------------------------------
-- RawMonad.op list-monad を op と省略して書く。
-- infixもそのまま使用できる。
open RawMonad list-monad

-- returnを直接使ってみる。
test1 : List ℕ
test1 = return zero

lem1 : {n : ℕ} -> (return n) ≡ (n ∷ [])    -- list Nat
lem1 = refl

-- bindを直接使ってみる。
lem2 : {n : ℕ} -> ((n ∷ []) >>= (\x -> x ∷ [])) ≡ (n ∷ []) -- list Nat
lem2 = refl

-- その他のMonadの関数を使ってみる。
lem3 : {n m : ℕ} -> (n ∷ [] >> m ∷ []) ≡ (m ∷ []) -- list Nat
lem3 = refl

lem4 : {n : ℕ} -> ((\x -> x ∷ []) =<< (n ∷ [])) ≡ (n ∷ []) -- list Nat
lem4 = refl

lem5 : {n : ℕ} -> join (return (return n)) ≡ return n
lem5 = refl

-- END
