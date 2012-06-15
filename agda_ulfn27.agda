{-
  Dependently Typed Programming in Agda
  Ulf Norell

  2.7 Modules
  2.8 Records
-}

module agda_ulfn27 where

module AgdaBasics where

data Bool : Set where
  true : Bool
  false : Bool

not : Bool -> Bool
not true = false
not false = true

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat

infixl 60 _*_
infixl 40 _+_

_+_ : Nat -> Nat -> Nat
zero + m = m
suc n + m = suc (n + m)

_*_ : Nat -> Nat -> Nat
zero * m = zero
suc n * m = m + (n * m)

infixr 40 _::_
data List (A : Set) : Set where
  [] : List A
  _::_ : A -> List A -> List A
 
_∘_ : {A : Set}{B : A -> Set}{C : (x : A) -> B x -> Set} -- \o
  (f : {x : A}(y : B x) -> C x y)
  (g : (x : A) -> B x)
  (x : A) -> C x (g x)
(f ∘ g) x = f (g x)

_<_ : Nat -> Nat -> Bool
_ < zero = false
zero < suc n = true
suc m < suc n = m < n


-- 2.7 Modules
module Maybe where
  data Maybe (A : Set) : Set where
    nothing : Maybe A
    just : A -> Maybe A

  maybe : {A B : Set} -> B -> (A -> B) -> Maybe A -> B
  maybe z f nothing = z
  maybe z f (just x) = f x

module A where
  private
    internal : Nat
    internal = zero

    exported : Nat -> Nat
    exported n = n + internal

mapMaybe1 : {A B : Set} -> (A -> B) -> Maybe.Maybe A -> Maybe.Maybe B
mapMaybe1 f Maybe.nothing = Maybe.nothing
mapMaybe1 f (Maybe.just x) = Maybe.just (f x)

mapMaybe2 : {A B : Set} -> (A -> B) -> Maybe.Maybe A -> Maybe.Maybe B
mapMaybe2 f m = let open Maybe in maybe nothing (just ∘ f) m

open Maybe

mapMaybe3 : {A B : Set} -> (A -> B) -> Maybe A -> Maybe B
mapMaybe3 f m = maybe nothing (just ∘ f) m

{-
同じモジュールを2重にopenできず、renameする前の名前は使えないようだ。
(see. ReferenceManual.Modules)

open Maybe using (maybe)
  renaming (Maybe to _option; nothing to none; just to some)
  -- option は後置オペレータにする。
mapOption : {A B : Set} -> (A -> B) -> A option -> B option
mapOption f none = none
mapOption f (some x) = some (f x)

mtrue : Maybe Bool
mtrue = mapOption not (just false)
-}

mapOption : {A B : Set} -> (A -> B) -> Maybe A -> Maybe B
mapOption f nothing = nothing
mapOption f (just x) = just (f x)

mtrue : Maybe Bool
mtrue = mapOption not (just false)

-- Sortモジュールを定義する。
module Sort (A : Set)(_<_ : A -> A -> Bool) where
  insert : A -> List A -> List A
  insert y [] = y :: []
  insert y (x :: xs) with x < y
  ... | true = x :: insert y xs
  ... | false = y :: x :: xs

  sort : List A -> List A
  sort [] = []
  sort (x :: xs) = insert x (sort xs)

-- Sortモジュールの外から、Openせずに使う。
sort1 : (A : Set)(_<_ : A -> A -> Bool) -> List A -> List A
sort1 = Sort.sort

-- SortNatモジュールを定義する。Sortモジュールに引数を与える。
module SortNat = Sort Nat _<_

-- SortNatモジュールの外から、Openせずに使う。
sort2 : List Nat -> List Nat
sort2 = SortNat.sort

-- Sortモジュールに引数を与えて、ついでに関数をリネームする。
open Sort Nat _<_ renaming (insert to insertNat; sort to sortNat)

{-
Sometimes you want to export the contents of another module from
the current module. In this case you can open the module publicly using
the public keyword:
-}
module Lists (A : Set)(_<_ : A -> A -> Bool) where
-- 他のモジュールを現在のモジュールで使う(exportする)。
  open Sort A _<_ public
  minimum : List A -> Maybe A
  minimum xs with sort xs
  ... | [] = nothing
  ... | y :: ys = just y

{-
Importing modules from other ﬁles Agda programs can be split over
multiple ﬁles. To use deﬁnitions from a module deﬁned in another ﬁle the
module has to be imported. Modules are imported by their names, so if
you have a module A.B.C in a ﬁle /some/local/path/A/B/C.agda it is
imported with the statement import A.B.C. In order for the system to
ﬁnd the ﬁle /some/local/path must be in Agda’s search path.
---
The search path can be set from emacs by executing M-x customize-group agda2.
-}

-- 2.8 Records
record Point : Set where
  field x : Nat
        y : Nat

mkPoint : Nat -> Nat -> Point
mkPoint a b = record{ x = a; y = b }

getX : Point -> Nat
getX = Point.x

abs2 : Point -> Nat
abs2 p = let open Point p in x * x + y * y

record Monad (M : Set -> Set) : Set1 where
  field
    return : {A : Set} -> A -> M A
    _>>=_ : {A B : Set} -> M A -> (A -> M B) -> M B

  mapM : {A B : Set} -> (A -> M B) -> List A -> M (List B)
  mapM f [] = return []

  mapM f (x :: xs) = f x >>= \y ->
    mapM f xs >>= \ys ->
    return (y :: ys)

mapM’ : {M : Set -> Set} -> Monad M ->
  {A B : Set} -> (A -> M B) -> List A -> M (List B)
mapM’ Mon f xs = Monad.mapM Mon f xs

-- END
