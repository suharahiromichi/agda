{-
  Dependently Typed Programming in Agda
  Ulf Norell
  3.2 Universes
  Universes for generic programming

  F-Algebraとしての説明を補ってみる。
  @suharahiromichi
  
  他の参考資料
  "Functional Programming with Bananas, Lenses, Envelopes, and Barbed Wire"
  http://homepages.inf.ed.ac.uk/wadler/papers/free-rectypes/free-rectypes.txt
-}

module agda_ulfn32_generic_falgebra where

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

data False : Set where
record True : Set where

data Functor : Set1 where
  |Id| : Functor
  |K| : Set -> Functor
  _|+|_ : Functor -> Functor -> Functor
  _|x|_ : Functor -> Functor -> Functor

data _⊕_ (A B : Set) : Set where
  inl : A -> A ⊕ B
  inr : B -> A ⊕ B

data _×_ (A B : Set) : Set where
  _,_ : A -> B -> A × B

infixr 50 _|+|_ _⊕_
infixr 60 _|x|_ _×_

[[_]] : Functor -> Set -> Set
[[ |Id| ]] X     = X
[[ |K| A ]] X    = A
[[ F |+| G ]] X  = [[ F ]] X ⊕ [[ G ]] X
[[ F |x| G ]] X  = [[ F ]] X × [[ G ]] X

{-
map' : (F : Functor){X Y : Set} -> (X -> Y) -> [[ F ]] X -> [[ F ]] Y
map' |Id| f x            = f x                  
map' (|K| A) f c         = c                    
map' (F |+| G) f (inl x) = inl (map' F f x)      
map' (F |+| G) f (inr y) = inr (map' G f y)      
map' (F |x| G) f (x , y) = map' F f x , map' G f y
-}

data µ_ (F : Functor) : Set where
  <_> : [[ F ]] (µ F) -> µ F

mapFold : forall {X} F G -> ([[ G ]] X -> X) -> [[ F ]] (µ G) -> [[ F ]] X
mapFold |Id|         G ϕ < x >   = ϕ (mapFold G G ϕ x)
mapFold (|K| A)      G ϕ c       = c
mapFold (F1 |+| F2 ) G ϕ (inl x) = inl (mapFold F1 G ϕ x)
mapFold (F1 |+| F2 ) G ϕ (inr y) = inr (mapFold F2 G ϕ y)
mapFold (F1 |x| F2 ) G ϕ (x , y) = mapFold F1 G ϕ x , mapFold F2 G ϕ y

-- fold
rec : {F : Functor} {A : Set} -> ([[ F ]] A -> A) -> µ F -> A
rec {F} ϕ < x > = ϕ (mapFold F F ϕ x)

[[_||_]] : {A B C : Set} -> (A -> C) -> (B -> C) -> A ⊕ B -> C
[[ f || g ]] (inl x) = f x
[[ f || g ]] (inr y) = g y

uncurry : {A B C : Set} -> (A -> B -> C) -> A × B -> C
uncurry f (x , y) = f x y

const : {A B : Set} -> A -> B -> A
const x y = x

{-
NatF NATの例
(1) 自己関手(型関手)Fを、NatFとする。
(2) 自然数の集合Nと、関数Z:1->N、S:N->NはF始代数である。
    対象Aは、NAT
    始対象の射は、[Z,S]
(3) 対象Bも、NAT
    F(f)は？

問題
  任意のbに対して、fを求める。

.            [Z,S]
NatF NAT ------------------->NatF NAT
  |                          |
  |                          |
  | F(f)                     | f = (|b|)
  |                          | を求める。
  v                          v
NatF NAT-------------------->NatF NAT
  .           b から、、、
-}

-- 型関手
NatF = |K| True |+| |Id|
-- 最小不動点と関手Fで構築された型は、F始代数とみなすことができる。
NAT = µ NatF

-- 始対象
Z : NAT
Z = < inl _ >

S : NAT -> NAT
S n = < inr n >

-- 代数bが、[m,S]の場合
plus' : NAT -> NAT -> NAT
plus' n m = rec [[ const m || S ]] n

-- 代数bが、[Z,plus' b]の場合
mult' : NAT -> NAT -> NAT
mult' a b = rec [[ const Z || plus' b ]] a

{-
ListF LISTの例
(1) 自己関手(型関手)Fを、ListFとする。
(2) 自然数の集合Nと、関数nil:1->LIST、cons:LIST->LISTはF始代数である。
    対象Aは、LIST
    始対象の射は、[nil,cons]
(3) 対象Bも、LIST
    F(f)は？

問題
  任意のbに対して、fを求める。

.            [nil,cons]
ListF LIST ----------------->ListF LIST
  |                          |
  |                          |
  | F(f)                     | f = (|b|)
  |                          | を求める。
  v                          v
ListF LIST------------------>ListF LIST
  .           b から、、、
-}

-- 型関手
ListF = \A -> |K| True |+| |K| A |x| |Id|
-- 最小不動点と関手Fで構築された型は、F始代数とみなすことができる。
LIST = \A -> µ (ListF A)

-- 始対象
nil : {A : Set} -> LIST A
nil = < inl _ >

cons : {A : Set} -> A -> LIST A -> LIST A
cons x xs = < inr (x , xs) >

-- 代数bが、[z,f]の場合
-- つまり、リストなら、任意の代数の場合fold関数となる。
foldr' : {A B : Set} -> (A -> B -> B) -> B -> LIST A -> B
foldr' {A}{B} f z = rec [[ const z || uncurry f ]]

-- END
