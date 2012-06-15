{-
  Maybe Monad モナド によるサザエさんの家族構成（磯野家）
  agda_stdlibの RawMonad をつかい、maybe-monadを生成してつかう。

  以下にあるcoqの例をそのまま使う。
  Functional Programming Memo, 28 OCTOBER, 2011
  http://study-func-prog.blogspot.jp/2011/10/coq-monads-in-coq.html

  Monad則の証明は、erutufさんのページのAlgebraic Reasoningを使用した。
  http://d.hatena.ne.jp/erutuf/
-}

module agda_maybe_monad where

open import Data.Nat
open import Data.Bool
open import Data.List
open import Function                        -- id

-- equality
data _≡_ {A : Set} (x : A) : A -> Set where
  refl : x ≡ x

----------------------------------
-- Maybe
--
data Maybe {a} (A : Set a) : Set a where
  some : (x : A) -> Maybe A
  nothing : Maybe A

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

father : Isono -> Maybe Isono
father sazae = some namihei
father katsuo = some namihei
father wakame = some namihei
father tara = some masuo
father _ = nothing

mother : Isono -> Maybe Isono
mother sazae = some fune
mother katsuo = some fune
mother wakame = some fune
mother tara = some sazae
mother _ = nothing

----------------------------------
-- Maybe Monad
--
open import Category.Monad

bind : ∀ {A} {B} -> Maybe A -> (A -> Maybe B) -> Maybe B
bind nothing _ = nothing
bind (some x) f = f x

maybe-monad : ∀ {A} -> RawMonad (Maybe {A})
maybe-monad = record {
    return = λ x -> some x;
    _>>=_ = bind
    }

open RawMonad maybe-monad
-- 以下、return と >>= を
-- RawMonad.return maybe-monad などと書かなくてよくする。

----------------------------------
-- Sample
--
-- f_of_m s = do x <- mother s; father x
f_of_m : Isono -> Maybe Isono
f_of_m s = mother s >>= father

-- m_of_f s = do x <- father s; mother x
m_of_f : Isono -> Maybe Isono
m_of_f s = father s >>= mother

f_of_f : Isono -> Maybe Isono
f_of_f s = father s >>= father

m_of_m : Isono -> Maybe Isono
m_of_m s = mother s >>= mother

f_of_f_of_f : Isono -> Maybe Isono
f_of_f_of_f s = father s >>= father >>= father
-- >>= は左結合

----------------------------------
-- test
--
lem1 : f_of_m tara ≡ some namihei
lem1 = refl

lem2 : f_of_m katsuo ≡ nothing
lem2 = refl

lem3 : f_of_f_of_f tara ≡ nothing
lem3 = refl

----------------------------------
-- モナド則の証明
--
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

-- 実際の証明

mr1 : forall {A} (x : A) (f : A -> Maybe A) -> ((return x) >>= f) == (f x)
mr1 f x = eqrefl

mr2 : forall {A} (mx : Maybe A) -> (mx >>= return) == mx
mr2 nothing = eqrefl
mr2 (some x) =                              -- eqreflだけでもよい。
  proof
  ((some x) >>= return)                     -- >==のほうが==[より優先度が低い
  ==[ eqrefl ]
  bind (some x) return
  ==[ eqrefl ]
  some x
  qed

mr3 : forall {A} (mx : Maybe A) (f g : A -> Maybe A) ->
  (mx >>= (\ x -> (f x >>= g))) == ((mx >>= f) >>= g)
mr3 nothing _ _ = eqrefl
mr3 (some x) f g =                          -- eqreflだけでもよい。
  proof
  ((some x) >>= (\ x -> (f x >>= g)))       -- >==のほうが==[より優先度が低い
  ==[ eqrefl ]
  bind (some x) (\ x -> (f x >>= g))
  ==[ eqrefl ]
  (\ x -> (f x >>= g)) x
  ==[ eqrefl ]
  (f x >>= g)
  ==[ eqrefl ]
  bind (f x) g
  ==[ eqrefl ]
  bind (bind (some x) f) g
  ==[ eqrefl ]
  (((some x) >>= f) >>= g)
  qed

-- END
