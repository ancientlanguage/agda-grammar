module Common.RoundTripReflexive where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Prelude.Monoidal.Exponential
open import Common.RoundTrip

open ⇒

rtRefl
  : {la : Level}
  → {A : Set la}
  → RoundTrip A A
rtRefl {A = A} = roundTrip idn idn p
  where
    p : (x : A) → x ≡ idn (idn x)
    p x = refl
