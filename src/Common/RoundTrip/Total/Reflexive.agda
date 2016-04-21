module Common.RoundTrip.Total.Reflexive where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Prelude.Monoidal.Exponential
open import Common.RoundTrip.Total.Definition

open ⇒

module ⟳ where

  reflexivity
    : {la : Level}
    → {A : Set la}
    → A ⟳ A
  reflexivity {A = A} = roundTrip idn idn p
    where
      p : (x : A) → x ≡ idn (idn x)
      p x = refl
