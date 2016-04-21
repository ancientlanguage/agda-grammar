module Common.RoundTrip.Partial.Map where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Prelude.Path
open import Prelude.Monoidal.Product.Indexed
open import Common.RoundTrip.Partial.Definition
open import Common.RoundTrip.Partial.Result

open Π
open ≡

module ↻ where
  map :
    {la lb le1 le2 : Level}
    → {A : Set la}
    → {B : Set lb}
    → {E1 : Set le1}
    → {E2 : Set le2}
    → (E1 → E2)
    → A ↻ B // E1
    → A ↻ B // E2
  map {B = B} f (roundTripPartial A→B⁇E1 B→A p) = roundTripPartial A→B⁇E2 B→A q
    where
      A→B⁇E2 = mapUndefined f ∘ A→B⁇E1

      q : (x : B) → defined x ≡ A→B⁇E2 (B→A x)
      q x = mapUndefined f · p x
