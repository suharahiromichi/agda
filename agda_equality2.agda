{--
  Agdaであそぼ
  @erutuf13
  http://www.slideshare.net/erutuf13/agda-9413777
  証明の内容はすこし異なる。
--}

module agda_equality2 where

-- open import Data.Nat
open import Function                        -- infixr 0 _$_
-- f $ x = f x

----------------------------------
-- 整数と加算と乗算の定義（Data.Natと同じ内容）
--
data ℕ : Set where
  zero : ℕ
  suc : ℕ -> ℕ

infixl 6 _+_
_+_ : ℕ → ℕ → ℕ
zero  + n = n
suc m + n = suc (m + n)

infixl 7 _*_
_*_ : ℕ → ℕ → ℕ
zero  * n = zero
suc m * n = n + m * n

infixr 4 _==_
_==_ : forall {A : Set} -> A -> A -> Set1
a == b = (P : _ -> Set) -> P a -> P b

----------------------------------
-- 証明で使う補助定理を証明しておく。
--
cong : forall {A : Set} -> (f : A -> A) -> {x y : A} -> x == y -> f x == f y
cong f x=y P = x=y (\y -> P (f y))

eqrefl : forall {A : Set} {x : A} -> x == x
eqrefl _ p = p

eqsym : forall {A : Set} {n m : A} -> n == m -> m == n
eqsym {A}{n}{m} n=m P = n=m (\l -> P l -> P n) (\x -> x)

eqtrans : forall {A : Set} {n m l : A} -> n == m -> m == l -> n == l
eqtrans n=m m=l P Pn = m=l P (n=m P Pn)

eqsuc : {n m : ℕ} -> n == m -> suc n == suc m
eqsuc n=m P = n=m (\ l -> P (suc l))

eqplus : (l n m : ℕ) -> n == m -> l + n == l + m
eqplus l n m n=m = cong (\x -> l + x) n=m

eqplus' : (n m l : ℕ) -> n == m -> n + l == m + l
eqplus' n m l n=m = cong (\x -> x + l) n=m

plusassoc : (n m l : ℕ) -> n + m + l == n + (m + l)
plusassoc zero _ _ = eqrefl
plusassoc (suc n) m l = cong suc $ (plusassoc n m l)

plusassoc' : (n m l : ℕ) -> n + (m + l) == n + m + l
plusassoc' zero _ _ = eqrefl
plusassoc' (suc n) m l = cong suc $ (plusassoc' n m l)
-- (eqsym (plusassoc m n l)) と同じである。

----------------------------------
-- erutuf13さんによる、==[]
--
infix  4 _IsEqualTo_
infix  2 _qed
infixr 2 _==[_]_
infix  1 proof_

data _IsEqualTo_ {A : Set} (x y : A) : Set1 where
    relTo : (x=y : x == y) -> x IsEqualTo y

proof_ : forall {A : Set} {x y : A} -> x IsEqualTo y -> x == y
proof relTo x=y = x=y

_==[_]_ : forall {A : Set} {y z : A} -> (x : A) -> x == y -> y IsEqualTo z -> x IsEqualTo z
_ ==[ x=y ] relTo y=z = relTo (eqtrans x=y y=z)

_qed : forall {A : Set} -> (x : A) -> x IsEqualTo x
_qed _ = relTo eqrefl

----------------------------------
-- 加算の可換則の証明
-- coq_nat_distr.v を参考とする。
-- もとはyoshihiroさんのページから
-- 
plus0 : (n : ℕ) -> n + zero == n
plus0 zero = eqrefl
plus0 (suc n) =
  proof
  suc n + zero
  ==[ eqrefl ]
  suc (n + zero)
  ==[ eqsuc (plus0 n) ]                 -- sucの中、帰納法の仮定より。
  suc n
  qed

plusSy : (n m : ℕ) -> n + suc m == suc (n + m)
plusSy zero _ = eqrefl
plusSy (suc n) m =
  proof
  suc n + suc m
  ==[ eqrefl ]
  suc (n + suc m)
  ==[ eqsuc (plusSy n m) ]              -- sucの中、帰納法の仮定より。
  suc (suc n + m)
  qed

pluscomm : (n m : ℕ) -> n + m == m + n
pluscomm n zero =
  proof
  n + zero
  ==[ plus0 n ]
  n
  ==[ eqrefl ]
  zero + n
  qed
pluscomm n (suc m) =
  proof
  n + suc m
  ==[ plusSy n m ]
  suc (n + m)
  ==[ eqsuc (pluscomm n m) ]            -- sucの中、帰納法の仮定より。
  suc (m + n)
  ==[ eqrefl ]
  suc m + n
  qed

----------------------------------
-- 証明
--
multS : (m n : ℕ) -> m + m * n == m * suc n
multS zero _ = eqrefl
multS (suc m) n =
  proof
  suc m + suc m * n
  ==[ eqrefl ]                              -- *の定義より。
  suc m + (n + m * n)
  ==[ eqsuc (eqsym (plusassoc m n (m * n))) ] -- sucの中
  suc (m + n + m * n)
  ==[ eqsuc (eqplus' (m + n) (n + m) (m * n) (pluscomm m n)) ]
  -- sucの中、最右の+の(m * n)の部分をのぞいて、pluscomm（可換則）を使う。
  suc (n + m + m * n)
  ==[ eqsuc (plusassoc n m (m * n)) ]       -- sucの中
  suc (n + (m + m * n))
  ==[ eqsuc (eqplus n (m + m * n) (m * suc n) (multS m n)) ]
  -- sucの中、最左の+のnの部分をのぞいて、(m + m * n)の部分にmultS m nを適用する。
  suc (n + m * suc n)
  ==[ eqrefl ]                              -- +の定義より。
  suc n + m * suc n
  ==[ eqrefl ]                              -- *の定義より。(suc n)をまとめる。
  suc m * suc n
  qed

-- appendとreverseの定義を使うところ(eqrefl)は省略できる。
multS' : (m n : ℕ) -> m + m * n == m * suc n
multS' zero _ = eqrefl
multS' (suc m) n =
  proof
  suc m + (n + m * n)
  ==[ eqsuc (eqsym (plusassoc m n (m * n))) ] -- sucの中
  suc (m + n + m * n)
  ==[ eqsuc (eqplus' (m + n) (n + m) (m * n) (pluscomm m n)) ]
  -- sucの中、最右の+の(m * n)の部分をのぞいて、pluscomm（可換則）を使う。
  suc (n + m + m * n)
  ==[ eqsuc (plusassoc n m (m * n)) ]       -- sucの中
  suc (n + (m + m * n))
  ==[ eqsuc (eqplus n (m + m * n) (m * suc n) (multS m n)) ]
  -- sucの中、最左の+のnの部分をのぞいて、(m + m * n)の部分にmultS m nを適用する。
  suc (n + m * suc n)
  qed

-- END
