{-# OPTIONS --without-K --safe --erased-cubical --no-import-sorts #-}

module SUtil where

open import Prelude

_∈_ : Name → List Name → Bool
n ∈ []       = false
n ∈ (x ∷ ns) = if n == x then true else n ∈ ns

-- treat list as set
insert : Name → List Name → List Name
insert n ns = if n ∈ ns then ns else n ∷ ns

lookup : {A : Type} → List (Name × List A) → Name → List A
lookup []             n = []
lookup ((m , x) ∷ xs) n = if n == m then x else lookup xs n

nameSet : List Name → List Name
nameSet = foldr insert []

iterate : {A : Type} → ℕ → (A → A) → A → A
iterate zero    f x = x
iterate (suc k) f x = iterate k f (f x)

2ⁿSpeed : ℕ → List Note → List Note
2ⁿSpeed n = map (iterate n doubleSpeed)

zipFull : {A : Type} → List (List A) → List (List A) → List (List A)
zipFull []          yss        = yss
zipFull xss@(_ ∷ _) []         = xss
zipFull (xs ∷ xss)  (ys ∷ yss) = (xs ++ ys) ∷ zipFull xss yss

_+1 : {n : ℕ} → Fin n → Fin n
_+1 {suc n} k = (suc (toℕ k)) mod (suc n)

emptyVec : {n : ℕ}{A : Type} → Vec (List A) n
emptyVec {zero}  = []
emptyVec {suc n} = [] ∷ emptyVec {n}

foldIntoVector : {n : ℕ} {A : Type} → List (List A) → Vec (List A) (suc n)
foldIntoVector {n} {A} xss = fiv fz emptyVec xss
  where fiv : Fin (suc n) → Vec (List A) (suc n) → List (List A) → Vec (List A) (suc n)
        fiv k xss []         = xss
        fiv k xss (ys ∷ yss) = fiv (k +1) (updateAt k (_++ ys) xss) yss
