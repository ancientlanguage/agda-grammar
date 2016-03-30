module Common.RoundTripPartialReflexive where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Prelude.Monoidal.Exponential
open import Prelude.Monoidal.Product.Indexed
open import Common.PartialResult
open import Common.RoundTripPartial

open Π using (_∘_)
open ⇒ using (idn)

roundTripPartialReflexive
  : {la le : Level}
  → {A : Set la}
  → {E : Set le}
  → A ↻ A ⁇ E
roundTripPartialReflexive {A = A} = equiv idnP idn p
  where
    idnP = defined ∘ idn
    p : (x : A) → defined x ≡ idnP (idn x)
    p x = refl
