module AncientLanguage.Common.List where

open import Agda.Builtin.Nat
open import Agda.Builtin.List using (List; []; _∷_) public

length : {A : Set} → List A → Nat
length [] = 0
length (_ ∷ xs) = suc (length xs)

append : {A : Set} → (xs ys : List A) → List A
append [] ys = ys
append (x ∷ xs) ys = x ∷ append xs ys

join : {A : Set} → List (List A) → List A
join [] = []
join (x ∷ xs) = append x (join xs)

map : {A B : Set} → (f : A → B) → (xs : List A) → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

joinMap : {A B : Set} → (f : A → List B) → (xs : List A) → List B
joinMap f [] = []
joinMap f (x ∷ xs) = append (f x) (joinMap f xs)

singleton : {A : Set} → A → List A
singleton x = x ∷ []
