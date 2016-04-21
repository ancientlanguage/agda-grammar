module Common.RoundTripReflexive where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Prelude.Monoidal.Exponential
open import Common.RoundTrip

open ⇒

module ⟳ where

  reflexivity
    : {la : Level}
    → {A : Set la}
    → RoundTrip A A
  reflexivity {A = A} = roundTrip idn idn p
    where
      p : (x : A) → x ≡ idn (idn x)
      p x = refl
