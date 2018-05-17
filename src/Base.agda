module Base where

infixr 4 _+_
infixr 5 _*_

data _+_ (A B : Set) : Set where
  inl : (a : A) → A + B
  inr : (b : B) → A + B

record _*_ (A B : Set) : Set where
  constructor pair
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

module +GroupAdjacent (A B : Set) where
  to-next : (ab : A + B) (result : List (List1 A + List1 B)) → List (List1 A + List1 B)
  to-next (inl a) []                       = inl (list1 a []) ∷ []
  to-next (inl a)        (inl as ∷ result) = inl (List1M.prepend a as) ∷ result
  to-next (inl a) result@(inr _ ∷ _)       = inl (list1 a []) ∷ result
  to-next (inr b) []                       = inr (list1 b []) ∷ []
  to-next (inr b) result@(inl _ ∷ _)       = inr (list1 b []) ∷ result
  to-next (inr b)        (inr bs ∷ result) = inr (List1M.prepend b bs) ∷ result

  to : List (A + B) → List (List1 A + List1 B)
  to [] = []
  to (x ∷ xs) = to-next x (to xs)

  from : List (List1 A + List1 B) → List (A + B)
  from-as : List A → List (List1 A + List1 B) → List (A + B)
  from-bs : List B → List (List1 A + List1 B) → List (A + B)

  from-as [] rest = from rest
  from-as (a ∷ as) rest = inl a ∷ from-as as rest

  from-bs [] rest = from rest
  from-bs (b ∷ bs) rest = inr b ∷ from-bs bs rest

  from [] = []
  from (inl (list1 a as) ∷ xs) = inl a ∷ from-as as xs
  from (inr (list1 b bs) ∷ xs) = inr b ∷ from-bs bs xs

  to-from : (result : List (List1 A + List1 B)) → to (from result) ≡ result
  to-from [] = refl
  to-from (inl (list1 a []) ∷ []) = refl
  to-from (inl (list1 a []) ∷ inl (list1 a₁ rest) ∷ result) = {!!}
  to-from (inl (list1 a []) ∷ inr bs ∷ result) = {!!}
  to-from (inl (list1 a (x ∷ rest)) ∷ result) = {!!}
  to-from (inr b ∷ result) = {!!}

  from-to : (input : List (A + B)) → from (to input) ≡ input
  from-to [] = refl
  from-to (inl a ∷ []) = refl
  from-to (inl a ∷ inl a2 ∷ input) = {!!}
  from-to (inl a ∷ inr b ∷ input) = {!!}
  from-to (inr b ∷ input) = {!!}
