module agda_zip_btree where
{-
  B-TreeのZipperをAgdaで実装してみた。
  Maybeを使用した(see. Wikibooks)ことを除いて、
  Learn You a Haskell for Great Good!
  と同じことをしている。
  
  Learn You a Haskell for Great Good!, Miran Lipovača
  14. Zippers
  http://learnyouahaskell.com/zippers
  
  taediumさん、F#でZipper、テストコードほか
  http://d.hatena.ne.jp/taedium/20110826/p1

  Zipper - HaskellWiki - Haskell  
  http://www.haskell.org/haskellwiki/Zipper
  
  Wikibooks Haskell/Zippers
  http://ja.wikibooks.org/wiki/Haskell/Zippers
-}

open import Data.Nat
open import Data.Bool
open import Data.List
open import Data.Char
open import Function                        -- id

-- data Tree a = Empty | Node a (Tree a) (Tree a) deriving (Show)
data Tree (A : Set) : Set where
  empty : Tree A
  node  : A -> Tree A -> Tree A -> Tree A

-- パンの切れ端、または、アリアドネの糸
-- data Crumb a = LeftCrumb a (Tree a) | RightCrumb a (Tree a) deriving (Show)
data Crumb (A : Set) : Set where
  L : A -> Tree A -> Crumb A                -- ノードA、右はTreeのとき、左に曲がったことをリストする。
  R : A -> Tree A -> Crumb A                -- ノードA、左はTreeのとき、右に曲がったことをリストする。

-- type Breadcrumbs a = [Crumb a]
-- type Zipper a = (Tree a, Breadcrumbs a) 
data Zipper (A : Set) : Set where
  z[_,_] : Tree A -> List (Crumb A) -> Zipper A

----------------------------------
-- Maybe
--
open import Category.Monad
data Maybe {a} (A : Set a) : Set a where
  some : (x : A) -> Maybe A
  nothing : Maybe A

bind : ∀ {A} {B} -> Maybe A -> (A -> Maybe B) -> Maybe B
bind nothing _ = nothing
bind (some x) f = f x

maybe-monad : ∀ {A} -> RawMonad (Maybe {A})
maybe-monad = record {
    return = λ x -> some x;
    _>>=_ = bind
    }

open RawMonad maybe-monad
-----------------------------------
-- Learn You a Haskell for Great Good! にしたがって、実装する。
--
-- goLeft :: (Tree a, Breadcrumbs a) -> (Tree a, Breadcrumbs a)
-- goLeft (Node x l r, bs) = (l, LeftCrumb x r:bs)
goLeft : {A : Set} -> Zipper A -> Maybe (Zipper A)
goLeft z[ node x l r , bs ] = some z[ l , L x r ∷ bs ]
goLeft z[ empty      , bs ] = nothing

-- goRight :: (Tree a, Breadcrumbs a) -> (Tree a, Breadcrumbs a)  
-- goRight (Node x l r, bs) = (r, RightCrumb x l:bs)  
goRight : {A : Set} -> Zipper A -> Maybe (Zipper A)
goRight z[ node x l r , bs ] = some z[ r , R x l ∷ bs ]
goRight z[ empty      , bs ] = nothing

-- goUp :: (Tree a, Breadcrumbs a) -> (Tree a, Breadcrumbs a)  
-- goUp (t, LeftCrumb x r:bs) = (Node x t r, bs)  
-- goUp (t, RightCrumb x l:bs) = (Node x l t, bs)  
goUp : {A : Set} -> Zipper A -> Maybe (Zipper A)
goUp z[ t , L x r ∷ bs ] = some z[ node x t r , bs ] -- Lにいったらtだったのを戻す。
goUp z[ t , R x l ∷ bs ] = some z[ node x l t , bs ] -- Rにいったらtだったのを戻す。
goUp z[ _ , _ ]          = nothing

-- modify :: (a -> a) -> Zipper a -> Zipper a
-- modify f (Node x l r, bs) = (Node (f x) l r, bs)
-- modify f (Empty, bs) = (Empty, bs)
modify : {A : Set} -> (A -> A) -> Zipper A -> Maybe (Zipper A)
modify f z[ node x l r , bs ] = some z[ node (f x) l r , bs ]
modify f z[ empty      , bs ] = some z[ empty , bs ]

-- attach :: Tree a -> Zipper a -> Zipper a
-- attach t (_, bs) = (t, bs)
attach : {A : Set} -> Tree A -> Zipper A -> Maybe (Zipper A)
attach t z[ _ , bs ] = some z[ t , bs ]

-- topMost :: Zipper a -> Zipper a
-- topMost (t,[]) = (t,[])
-- topMost z = topMost (goUp z)
topMost : {A : Set} -> Zipper A -> Maybe (Zipper A)
topMost z[ t , [] ] = some z[ t , [] ]
topMost z           = goUp z >>= topMost

-- テストコード
freeTree : Tree Char
freeTree = 
         node 'P'
         (node 'O'
           (node 'L'
             (node 'N' empty empty)
             (node 'T' empty empty)
           )
           (node 'Y'
             (node 'S' empty empty)
             (node 'A' empty empty)
           )
         )
         (node 'L'
           (node 'W'
             (node 'C' empty empty)
             (node 'R' empty empty)
           )
           (node 'A'
             (node 'A' empty empty)
             (node 'C' empty empty)
           )
         )

mkzip : {A : Set} -> Tree A -> Maybe (Zipper A)
mkzip t = some z[ t , [] ]

nodechar : Zipper Char -> Maybe Char
nodechar z[ node x _ _ , _ ] = some x
nodechar z[ empty      , _ ] = nothing

data _≡_ {A : Set} (x : A) : A -> Set where
  refl : x ≡ x

test1 : (mkzip freeTree >>= goLeft >>= goRight >>=
  goUp >>= nodechar) ≡ return 'O'
test1 = refl

test2 : (mkzip freeTree >>= goLeft >>= goRight >>=
  modify (\ x -> 'Z') >>= nodechar) ≡ return 'Z'
test2 = refl

test3 : (mkzip freeTree >>= goLeft >>= goLeft >>=
  goLeft >>= topMost >>= nodechar) ≡ return 'P'
test3 = refl

test4 : (mkzip freeTree >>= goLeft >>= goLeft >>= goLeft >>= goLeft >>=
  attach (node 'Z' empty empty) >>= nodechar) ≡ return 'Z'
test4 = refl

test5 : (mkzip freeTree >>= goRight >>= goRight >>= goUp >>= goUp >>=
  goRight >>= goRight >>= nodechar) ≡ return 'A'
test5 = refl

-- END
