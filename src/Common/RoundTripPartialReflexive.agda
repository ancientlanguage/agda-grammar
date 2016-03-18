module Common.RoundTripPartialReflexive where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Prelude.Function
open import Common.PartialResult
open import Common.RoundTripPartial

roundTripReflexive
  : {la le : Level}
  → {A : Set la}
  → {E : Set le}
  → A ↻ A ⁇ E
roundTripReflexive {A = A} = equiv idP id p
  where
    idP = defined ∘ id
    p : (x : A) → defined x ≡ idP (id x)
    p x = refl
