module Common.RoundTrip.Total.Reflexive where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Prelude.Monoidal.Exponential
open import Common.RoundTrip.Total.Definition

module ⟳ where
  reflexivity
    : {la : Level}
    → {A : Set la}
    → A ⟳ A
  reflexivity = roundTrip ⇒.idn ⇒.idn (λ x → refl)
