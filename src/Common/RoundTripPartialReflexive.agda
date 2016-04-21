module Common.RoundTripPartialReflexive where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Prelude.Monoidal.Exponential
open import Prelude.Monoidal.Product.Indexed
open import Common.PartialResult
open import Common.RoundTripPartial

open Π using (_∘_)
open ⇒ using (idn)

rtpRefl
  : {le la : Level}
  → {E : Set le}
  → {A : Set la}
  → A ↻ A // E
rtpRefl {A = A} = roundTripPartial idnP idn p
  where
    idnP = defined ∘ idn
    p : (x : A) → defined x ≡ idnP (idn x)
    p x = refl
