{--
  golb erutuf
  証明を読みやすく書きやすく
  http://d.hatena.ne.jp/erutuf/20110205/1296923573
--}

module agda_equality3 where

open import Function                        -- infixr 0 _$_
-- f $ x = f x

infixr 6 _==_

_==_ : forall {A : Set} -> A -> A -> Set1
a == b = (P : _ -> Set) -> P a -> P b

eqrefl : forall {A : Set} {x : A} -> x == x
eqrefl _ p = p

eqtrans : forall {A : Set} {n m l : A} -> n == m -> m == l -> n == l
eqtrans n=m m=l P Pn = m=l P (n=m P Pn)

cong : forall {A : Set} -> (f : A -> A) -> {x y : A} -> x == y -> f x == f y
cong f x=y P = x=y (\y -> P (f y))

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

infixr 7 _++_
infixr 8 _::_

data List (A : Set) : Set where
    [] : List A
    _::_ : A -> List A -> List A

_++_ : forall {A : Set} -> List A -> List A -> List A
[]        ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

appNil : forall {A : Set} {l : List A} -> l == l ++ []
appNil {A}{[]} = eqrefl
appNil {A}{(x :: xs)} = cong (_::_ x) $ appNil

eqapp : forall {A : Set} {xs ys : List A} -> (zs : List A) -> xs == ys -> zs ++ xs == zs ++ ys
eqapp zs p = cong (\l -> zs ++ l) p

eqapp' : forall {A : Set} {xs ys : List A} -> (zs : List A) -> xs == ys -> xs ++ zs == ys ++ zs
eqapp' zs p = cong (\l -> l ++ zs) p

appAssoc : forall {A : Set} -> (xs ys zs : List A) -> (xs ++ ys) ++ zs == xs ++ ys ++ zs
appAssoc [] _ _ = eqrefl
appAssoc (x :: xs) ys zs = cong (_::_ x) $ appAssoc xs ys zs

reverse : forall {A : Set} -> List A -> List A
reverse [] = []
reverse (x :: xs) = reverse xs ++ (x :: [])

revApp : forall {A : Set} -> (l l' : List A) -> reverse (l ++ l') == reverse l' ++ reverse l
revApp [] _ = appNil
revApp (x :: xs) ys =
    proof                                   -- 題意より。
      reverse ((x :: xs) ++ ys)
    ==[ eqrefl ]                            -- appendの定義より。
      reverse (x :: (xs ++ ys))
    ==[ eqrefl ]                            -- reverseの定義より。
      (reverse (xs ++ ys)) ++ (x :: [])
    ==[ eqapp' (x :: []) $ revApp xs ys ]   -- ++右の(x::[])以外の部分に、revAppを適用する。
      (reverse ys ++ reverse xs) ++ (x :: [])
    ==[ appAssoc (reverse ys) (reverse xs) (x :: []) ] -- 結合律、文字とおり
      reverse ys ++ (reverse xs ++ (x :: []))
    ==[ eqrefl ]                            -- reverseの定義より。
      reverse ys ++ reverse (x :: xs)
    qed

-- appendとreverseの定義を使うところ(eqrefl)は省略できる。
revApp' : forall {A : Set} -> (l l' : List A) -> reverse (l ++ l') == reverse l' ++ reverse l
revApp' [] _ = appNil
revApp' (x :: xs) ys =
    proof
      (reverse (xs ++ ys)) ++ (x :: [])
    ==[ eqapp' (x :: []) $ revApp xs ys ]   -- ++右の(x::[])以外の部分に、revAppを適用する。
      (reverse ys ++ reverse xs) ++ (x :: [])
    ==[ appAssoc (reverse ys) (reverse xs) (x :: []) ] -- 結合律、文字とおり
      reverse ys ++ (reverse xs ++ (x :: []))
    qed

eqRev : forall {A : Set} -> (l : List A) -> reverse (reverse l) == l
eqRev [] = eqrefl
eqRev (x :: xs) =
    proof                                   -- 題意より。
      reverse (reverse (x :: xs))
    ==[ eqrefl ]                            -- reverseの定義より。
      reverse (reverse xs ++ (x :: []))
    ==[ revApp (reverse xs) (x :: []) ]     -- revAppで、(reverse xs) と (x :: []) に分解する。
      reverse (x :: []) ++ reverse (reverse xs)
    ==[ eqapp (reverse (x :: [])) $ eqRev xs ] -- ++の右の(reverse (x :: []))以外の部分に、eqRevを適用する。
      (x :: []) ++ xs
    ==[ eqrefl ]                            -- appendの定義より。
      x :: xs
    qed

-- appendとreverseの定義を使うところ(eqrefl)は省略できる。
eqRev' : forall {A : Set} -> (l : List A) -> reverse (reverse l) == l
eqRev' [] = eqrefl
eqRev' (x :: xs) =
    proof
      reverse (reverse xs ++ (x :: []))
    ==[ revApp (reverse xs) (x :: []) ]     -- revAppで、(reverse xs) と (x :: []) に分解する。
      reverse (x :: []) ++ reverse (reverse xs)
    ==[ eqapp (reverse (x :: [])) $ eqRev xs ] -- ++の右の(reverse (x :: []))以外の部分に、eqRevを適用する。
      (x :: []) ++ xs
    qed

-- END
