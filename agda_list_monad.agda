{-
  List Monad モナド によるサザエさんの家族構成（磯野家）
  agda_stdlibの RawMonad をつかい、list-monadを生成してつかう。

  以下にあるcoqの例をそのまま使う。
  Functional Programming Memo, 28 OCTOBER, 2011
  http://study-func-prog.blogspot.jp/2011/10/coq-monads-in-coq.html

  Monad則の証明は、erutufさんのページのAlgebraic Reasoningを使用した。
  http://d.hatena.ne.jp/erutuf/
-}

module agda_list_monad where

open import Data.Nat
open import Data.Bool
open import Data.List
open import Function                        -- id

-- Leibnitz equality
data _≡_ {A : Set} (x : A) : A -> Set where
  refl : x ≡ x

----------------------------------
-- 磯野家
--
data Isono : Set where
  namihei : Isono
  fune : Isono
  masuo : Isono
  sazae : Isono
  katsuo : Isono
  wakame : Isono
  tara : Isono

children : Isono -> List Isono
children namihei = sazae ∷ katsuo ∷ wakame ∷ []
children fune = sazae ∷ katsuo ∷ wakame ∷ []
children masuo = tara ∷ []
children sazae = tara ∷ []
children _ = []

----------------------------------
-- List Monad
--
open import Category.Monad

bind : ∀ {A B} → List A → (A → List B) → List B
bind [] _ = []
bind (x ∷ xs) f = (f x) ++ (bind xs f)

list-monad : ∀ {A} -> RawMonad (List {A})
list-monad = record {
    return = λ x -> x ∷ [];
    _>>=_  = bind
    }

open RawMonad list-monad
-- 以下、return と >>= を
-- RawMonad.return list-monad などと書かなくてよくする。

----------------------------------
-- Sample
--
-- grandchildren s = do x <- children s; children x
grandchildren : Isono -> List Isono
grandchildren s = children s >>= children

----------------------------------
-- test
--
lem1 : grandchildren fune ≡ (tara ∷ [])
lem1 = refl

lem2 : grandchildren katsuo ≡ []
lem2 = refl

----------------------------------
-- モナド則の証明
--
-- open import agda_equality3

infixr 4 _==_
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

appNil : forall {A : Set} {l : List A} -> l == l ++ []
appNil {A}{[]} = eqrefl
appNil {A}{(x ∷ xs)} = cong (_∷_ x) $ appNil

eqapp : forall {A : Set} {xs ys : List A} -> (zs : List A) -> xs == ys -> zs ++ xs == zs ++ ys
eqapp zs p = cong (\l -> zs ++ l) p

eqapp' : forall {A : Set} {xs ys : List A} -> (zs : List A) -> xs == ys -> xs ++ zs == ys ++ zs
eqapp' zs p = cong (\l -> l ++ zs) p

appAssoc : forall {A : Set} -> (xs ys zs : List A) -> (xs ++ ys) ++ zs == xs ++ ys ++ zs
appAssoc [] _ _ = eqrefl
appAssoc (x ∷ xs) ys zs = cong (_∷_ x) $ appAssoc xs ys zs

mr1 : forall {A} -> (x : A) -> (f : A -> List A) -> (f x) == ((return x) >>= f)
mr1 x f =
  proof
  f x
  ==[ appNil ]
  ((f x) ++ [])
  qed

mr2 : forall {A} (mx : List A) -> (mx >>= return) == mx
mr2 [] = eqrefl
mr2 (x ∷ mx) =
  proof
  ((x ∷ mx) >>= return)
  ==[ eqrefl ]
  bind (x ∷ mx) (\ x -> x ∷ [])
  ==[ eqrefl ]
  ((\ x -> x ∷ []) x) ++ (bind mx  (\ x -> x ∷ []))
  ==[ eqrefl ]
  (x ∷ []) ++ (bind mx  (\ x -> x ∷ []))
  ==[ eqrefl ]
  (x ∷ []) ++ (mx >>= return)
  ==[ eqapp (x ∷ []) (mr2 mx) ]
  (x ∷ []) ++ mx
  ==[ eqrefl ]
  x ∷ mx
  qed

lem3 : forall {A} (mx my : List A) (f : A -> List A) ->
  (bind mx f) ++ (bind my f) == bind (mx ++ my) f
lem3 [] my _ = eqrefl
lem3 (x ∷ mx) my f =
  proof
  (bind (x ∷ mx) f) ++ (bind my f)
  ==[ eqrefl ]
  ((f x) ++ (bind mx f)) ++ (bind my f)
  ==[ appAssoc (f x) (bind mx f) (bind my f) ]
  (f x) ++ ((bind mx f) ++ (bind my f))
  ==[ eqapp (f x) (lem3 mx my f) ]
  (f x) ++ (bind (mx ++ my) f)
  ==[ eqrefl ]
  bind (x ∷ (mx ++ my)) f
  ==[ eqrefl ]                              -- appendの定義
  bind ((x ∷ mx) ++ my) f
  qed

mr3 : forall {A} (mx : List A) (f g : A -> List A) ->
  (mx >>= (\ x -> f x >>= g)) == ((mx >>= f) >>= g)
mr3 [] _ _ = eqrefl
mr3 (x ∷ mx) f g =
  proof
  ((x ∷ mx) >>= (\ x -> f x >>= g))  -- >==のほうが==[より優先度が低い
  ==[ eqrefl ]
  bind (x ∷ mx) (\ x -> f x >>= g)
  ==[ eqrefl ]
  ((\ x -> f x >>= g) x) ++ (bind mx (\ x -> f x >>= g))
  ==[ eqrefl ]
  (f x >>= g) ++ (bind mx (\ x -> f x >>= g))
  ==[ eqrefl ]
  (f x >>= g) ++ (mx >>= (\ x -> f x >>= g))
  ==[ eqapp (f x >>= g) (mr3 mx f g) ]
  (f x >>= g) ++ ((mx >>= f) >>= g)
  ==[ eqrefl ]
  (bind (f x) g) ++ (bind (mx >>= f) g)
  ==[ lem3 (f x) (mx >>= f) g ]
  bind ((f x) ++ (mx >>= f)) g
  ==[ eqrefl ]
  ((x ∷ mx >>= f) >>= g)
  qed

-- END
