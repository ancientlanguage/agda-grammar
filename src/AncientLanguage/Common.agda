module AncientLanguage.Common where

open import Agda.Builtin.Equality public
open import Agda.Builtin.Nat using (Nat; zero; suc) public

import AncientLanguage.Common.List
module List = AncientLanguage.Common.List
open List using (List; []; _∷_) public

infixl 7 _×_
infixl 6 _+_
infixl 1 _∘_

data ⊥ : Set where
open import Agda.Builtin.Unit public

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

data _+_ (A B : Set) : Set where
  inl : A → A + B
  inr : B → A + B

_∘_ : {A B C : Set} → (B → C) → (A → B) → A → C
(f ∘ g) x = f (g x)

traverse : {A B : Set} → List (A + B) → List A + List B
traverse [] = inr []
traverse (x ∷ xs) with x | traverse xs
... | inl x' | inl xs' = inl (x' ∷ xs')
... | inl x' | inr ys = inl (x' ∷ [])
... | inr y | inl xs' = inl xs'
... | inr y | inr ys = inr (y ∷ ys)

overInl : {A B C : Set} → (A → B) → A + C → B + C
overInl f (inl x) = inl (f x)
overInl f (inr x) = inr x

overInr : {A B C : Set} → (B → C) → A + B → A + C
overInr f (inl x) = inl x
overInr f (inr x) = inr (f x)
