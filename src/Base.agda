module Base where

infixr 4 _+_
infixr 5 _×_
infix 1 _,_
infix 1 _~_

record ⊤ : Set where
  constructor tt

data _+_ (A B : Set) : Set where
  inl : (a : A) → A + B
  inr : (b : B) → A + B

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

open import Agda.Builtin.List
open import Agda.Builtin.Nat
  using (Nat)
  using (zero)
  using (suc)
open import Agda.Builtin.Equality

record _~_ (A B : Set) : Set where
  field
    to : A → B
    from : B → A
    to-from : (b : B) → to (from b) ≡ b
    from-to : (a : A) → from (to a) ≡ a

module +Comm (A B : Set) where
  to : (A + B) → (B + A)
  to (inl a) = (inr a)
  to (inr b) = (inl b)
  
  from : (B + A) → (A + B)
  from (inl b) = (inr b)
  from (inr a) = (inl a)

  to-from : (ba : B + A) → to (from ba) ≡ ba
  to-from (inl b) = refl
  to-from (inr a) = refl

  from-to : (ab : A + B) → from (to ab) ≡ ab
  from-to (inl a) = refl
  from-to (inr b) = refl

+comm : {A B : Set} → (A + B) ~ (B + A)
+comm {A} {B} = record { +Comm A B }

data _×N_ (A : Set) : Nat → Set where
  none : A ×N zero
  add : (a : A) {n : Nat} (rest : A ×N n) → A ×N (suc n)

data List_≥_ (A : Set) (n : Nat) : Set where
  list≥ : (initial : A ×N n) (rest : List A) → List A ≥ n

data List1 (A : Set) : Set where
  list1 : (a : A) (rest : List A) → List1 A

module List1M where
  prepend : {A : Set} (a : A) (list : List1 A) → List1 A
  prepend a (list1 a2 rest) = list1 a (a2 ∷ rest)

module ×List (A : Set) where
  to : List A → ⊤ + A × List A
  to [] = inl _
  to (x ∷ xs) = inr (x , xs)

  from : ⊤ + A × List A → List A
  from (inl tt) = []
  from (inr (x , xs)) = x ∷ xs

  to-from : (x : ⊤ + A × List A) → to (from x) ≡ x
  to-from (inl tt) = refl
  to-from (inr (x , xs)) = refl

  from-to : (xs : List A) → from (to xs) ≡ xs
  from-to [] = refl
  from-to (x ∷ xs) = refl

×List : {A : Set} → List A ~ ⊤ + A × List A
×List {A} = record { ×List A }
