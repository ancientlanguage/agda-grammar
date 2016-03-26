module Common.RoundTripReflexive where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Prelude.Monoidal.Exponential
open import Common.RoundTrip

open ⇒

roundTripReflexive
  : {la : Level}
  → {A : Set la}
  → A ⟳ A
roundTripReflexive {A = A} = equiv idn idn p
  where
    p : (x : A) → x ≡ idn (idn x)
    p x = refl
