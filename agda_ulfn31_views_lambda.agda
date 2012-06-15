module agda_ulfn31_views_lambda where

open import Data.Nat

-- Indexing into a list

infixr 40 _::_
data List (A : Set) : Set where
  [] : List A
  _::_ : A -> List A -> List A

data _∈_ {A : Set}(x : A) : List A -> Set where -- \in
  hd : forall {xs} -> x ∈ x :: xs
  tl : forall {y xs} -> x ∈ xs -> x ∈ y :: xs

index : forall {A}{x : A}{xs} -> x ∈ xs -> ℕ
index (hd {xs}) = zero
index (tl {y}{xs} p) = suc (index {xs = xs} p)

length : {A : Set} -> List A -> ℕ
length [] = zero
length (x :: xs) = suc (length xs)

data Lookup {A : Set}(xs : List A) : ℕ -> Set where
  inside : (x : A)(p : x ∈ xs) -> Lookup xs (index p)
  outside : (m : ℕ) -> Lookup xs (length xs + m)

_!_ : {A : Set}(xs : List A)(n : ℕ) -> Lookup xs n
[] ! n           = outside n
(x :: xs) ! zero = inside x hd
(x :: xs) ! suc n             with xs ! n
(x :: xs) ! suc .(index p)       | inside y p = inside y (tl p)
(x :: xs) ! suc .(length xs + n) | outside n  = outside n

-- A type checker for lambda-calculus

infixr 30 _⇒_
data Type : Set where
  ı : Type
  _⇒_ : Type -> Type -> Type

data Equal? : Type -> Type -> Set where
  yes : forall {τ} -> Equal? τ τ
  no : forall {σ τ} -> Equal? σ τ

_=?=_ : (σ τ : Type) -> Equal? σ τ
ı =?= ı = yes
ı =?= (_ ⇒ _) = no
(_ ⇒ _) =?= ı = no
(σ1 ⇒ τ1) =?= (σ2 ⇒ τ2) with σ1 =?= σ2 | τ1 =?= τ2
(σ ⇒ τ) =?= (.σ ⇒ .τ) | yes | yes = yes
(σ1 ⇒ τ1) =?= (σ2 ⇒ τ2) | _ | _ = no

infixl 80 _$_
data Raw : Set where
  var : ℕ -> Raw         -- de Bruijn Index(Nat)から、変数の値を得る。
  _$_ : Raw -> Raw -> Raw
  lam : Type -> Raw -> Raw

Cxt = List Type

data Term (Γ : Cxt) : Type -> Set where
  var : forall {τ} -> τ ∈ Γ -> Term  Γ τ
  _$_ : forall {σ τ} -> Term Γ (σ ⇒ τ) -> Term Γ σ -> Term Γ τ
  lam : forall σ {τ} -> Term (σ :: Γ) τ -> Term Γ (σ ⇒ τ)
  -- σは、de Bruijn indexの「1」にあたるので、先頭に追加する。

erase : forall {Γ τ} -> Term Γ τ -> Raw
erase (var x) = var (index x) -- de Bruijn Indexを求める。
erase (t $ u) = erase t $ erase u
erase (lam σ t) = lam σ (erase t)

data Infer (Γ : Cxt) : Raw -> Set where
  ok : (τ : Type)(t : Term Γ τ) -> Infer Γ (erase t)
  bad : {e : Raw} -> Infer Γ e

infer : (Γ : Cxt)(e : Raw) -> Infer Γ e
infer Γ (var n)            with Γ ! n
infer Γ (var .(length Γ + n)) | outside n = bad
infer Γ (var .(index x))      | inside σ x = ok σ (var x)

infer Γ (e1 $ e2)                with infer Γ e1
infer Γ (e1 $ e2)                   | bad = bad
infer Γ (.(erase t1) $ e2)          | ok ı t1 = bad
infer Γ (.(erase t1) $ e2)          | ok (σ ⇒ τ) t1
                                                  with infer Γ e2
infer Γ (.(erase t1) $ e2)          | ok (σ ⇒ τ) t1 | bad = bad
infer Γ (.(erase t1) $ .(erase t2)) | ok (σ ⇒ τ) t1 | ok σ’ t2
                                                              with σ =?= σ’
infer Γ (.(erase t1) $ .(erase t2)) | ok (σ ⇒ τ) t1 | ok .σ t2  | yes = ok τ (t1 $ t2)
infer Γ (.(erase t1) $ .(erase t2)) | ok (σ ⇒ τ) t1 | ok σ’ t2 | no = bad

infer Γ (lam σ e)       with infer (σ :: Γ) e
infer Γ (lam σ .(erase t)) | ok τ t = ok (σ ⇒ τ) (lam σ t)
infer Γ (lam σ e)          | bad = bad

-- END
