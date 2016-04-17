module Common.ListFold where

open import Agda.Primitive
open import Agda.Builtin.List
open import Agda.Builtin.Equality

data _⊕_ {ℓ₀ ℓ₁} (A : Set ℓ₀) (B : Set ℓ₁) : Set (ℓ₀ ⊔ ℓ₁) where
  inl : A → A ⊕ B
  inr : B → A ⊕ B

foldr
  : {la lb : Level}
  → {A : Set la}
  → {B : Set lb}
  → (A → B → B)
  → B
  → List A
  → B
foldr f d [] = d
foldr f d (a ∷ as) = f a (foldr f d as) 

data A-Any : Set where
  a1 : A-Any
  a2 : A-Any
  a3 : A-Any

data A-Limit : Set where
  a1 : A-Limit
  a2 : A-Limit
  a2-a3 : A-Limit

data A-Temp : Set where
  a3-rest : List A-Limit → A-Temp
  a1-a3 : A-Temp
  a3-a3 : A-Temp

anyToLimitFolder
  : A-Any
  → A-Temp ⊕ List A-Limit
  → A-Temp ⊕ List A-Limit
anyToLimitFolder a2 (inl (a3-rest ys)) = inr (a2-a3 ∷ ys)
anyToLimitFolder a1 (inr ys) = inr (a1 ∷ ys)
anyToLimitFolder a2 (inr ys) = inr (a2 ∷ ys)
anyToLimitFolder a3 (inr ys) = inl (a3-rest ys)
anyToLimitFolder a1 (inl (a3-rest _)) = inl a1-a3
anyToLimitFolder a3 (inl (a3-rest _)) = inl a3-a3
anyToLimitFolder _ (inl e) = inl e

anyToLimit
  : List A-Any
  → A-Temp ⊕ List A-Limit
anyToLimit = foldr anyToLimitFolder (inr [])

anyToLimitR
  : List A-Any
  → A-Temp ⊕ List A-Limit
anyToLimitR [] = inr []
anyToLimitR (x ∷ xs) with anyToLimitR xs
anyToLimitR (a1 ∷ xs) | inl (a3-rest _) = inl a1-a3
anyToLimitR (a1 ∷ xs) | inl e = inl e
anyToLimitR (a2 ∷ xs) | inl (a3-rest ys) = inr (a2-a3 ∷ ys)
anyToLimitR (a2 ∷ xs) | inl e = inl e
anyToLimitR (a3 ∷ xs) | inl (a3-rest x) = inl a3-a3
anyToLimitR (a3 ∷ xs) | inl e = inl e 
anyToLimitR (a1 ∷ xs) | inr ys = inr (a1 ∷ ys)
anyToLimitR (a2 ∷ xs) | inr ys = inr (a2 ∷ ys)
anyToLimitR (a3 ∷ xs) | inr ys = inl (a3-rest ys)

limitToAny
  : List A-Limit
  → List A-Any
limitToAny [] = []
limitToAny (a1 ∷ xs) = a1 ∷ limitToAny xs
limitToAny (a2 ∷ xs) = a2 ∷ limitToAny xs
limitToAny (a2-a3 ∷ xs) = a2 ∷ a3 ∷ limitToAny xs

roundTripPartial
  : (xs : List A-Limit)
  → inr xs ≡ anyToLimitR (limitToAny xs)
roundTripPartial [] = refl
roundTripPartial (a1 ∷ xs) with anyToLimitR (limitToAny xs) | roundTripPartial xs
… | .(inr xs) | refl = refl
roundTripPartial (a2 ∷ xs) with anyToLimitR (limitToAny xs) | roundTripPartial xs
… | .(inr xs) | refl = refl
roundTripPartial (a2-a3 ∷ xs) with anyToLimitR (limitToAny xs) | roundTripPartial xs
… | .(inr xs) | refl = refl

roundTripPartial'
  : (xs : List A-Limit)
  → inr xs ≡ anyToLimit (limitToAny xs)
roundTripPartial' [] = refl
roundTripPartial' (a1 ∷ xs) with anyToLimit (limitToAny xs) | roundTripPartial' xs
roundTripPartial' (a1 ∷ xs) | .(inr xs) | refl = refl
roundTripPartial' (a2 ∷ xs) with anyToLimit (limitToAny xs) | roundTripPartial' xs
roundTripPartial' (a2 ∷ xs) | .(inr xs) | refl = refl
roundTripPartial' (a2-a3 ∷ xs)  with anyToLimit (limitToAny xs) | roundTripPartial' xs
roundTripPartial' (a2-a3 ∷ xs) | .(inr xs) | refl = refl

value1 : List A-Any
value1 = a1 ∷ a2 ∷ a3 ∷ []

value1L : List A-Limit
value1L = a1 ∷ a2-a3 ∷ []

test1 : inr value1L ≡ anyToLimit value1
test1 = refl
