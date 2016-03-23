module Common.RoundTripReflexive where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Common.Identity
open import Common.RoundTrip

roundTripReflexive
  : {la : Level}
  → {A : Set la}
  → A ⟳ A
roundTripReflexive {A = A} = equiv id id p
  where
    p : (x : A) → x ≡ id (id x)
    p x = refl
