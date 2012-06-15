module agda_ulfn31_views_find where

open import Function
open import Data.List
open import Data.Bool

data False : Set where
record True : Set where

IsTrue : Bool -> Set
IsTrue true  = True
IsTrue false = False

-- http://code.haskell.org/Agda/benchmark/ac/Bool.agda
IsFalse : Bool -> Set
IsFalse x = IsTrue (not x)

infixr 30 _:all:_
data All {A : Set}(P : A -> Set) : List A -> Set where
  all[] : All P []
  _:all:_ : forall {x xs} -> P x -> All P xs -> All P (x ∷ xs) -- \::

satisfies : {A : Set} -> (A -> Bool) -> A -> Set
satisfies p x = IsTrue (p x)

data Find {A : Set}(p : A -> Bool) : List A -> Set where
  found : (xs : List A)(y : A) -> satisfies p y -> (ys : List A) -> Find p (xs ++ y ∷ ys)
  not-found : forall {xs} -> All (satisfies (not ∘ p)) xs -> Find p xs

data _==_ {A : Set}(x : A) : A -> Set where
  refl : x == x

data Inspect {A : Set}(x : A) : Set where
  it : (y : A) -> x == y -> Inspect x

inspect : {A : Set}(x : A) -> Inspect x
inspect x = it x refl

trueIsTrue : {x : Bool} -> x == true -> IsTrue x
trueIsTrue refl = _

falseIsFalse : {x : Bool} -> x == false -> IsFalse x
falseIsFalse refl = _

find : {A : Set}(p : A -> Bool)(xs : List A) -> Find p xs
find p [] = not-found all[]
find p (x ∷ xs) with inspect (p x)
... | it true prf = found [] x (trueIsTrue prf) xs
... | it false prf with find p xs
find p (x ∷ ._) | it false _ | found xs y py ys =
  found (x ∷ xs) y py ys
find p (x ∷ xs) | it false prf | not-found npxs =
  not-found ((falseIsFalse prf) :all: npxs)

-- END
