module Common.RoundTrip.Partial.Reflexive where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Prelude.Monoidal.Exponential
open import Prelude.Monoidal.Product.Indexed
open import Common.RoundTrip.Partial.Result
open import Common.RoundTrip.Partial.Definition

open Π using (_∘_)
open ⇒ using (idn)

module ↻ where
  reflexivity
    : {le la : Level}
    → {E : Set le}
    → {A : Set la}
    → A ↻ A // E
  reflexivity {A = A} = roundTripPartial there idn again
    where
      there = defined ∘ idn
      again
        : (x : A)
        → there (idn x) ≡ defined x
      again x = refl
