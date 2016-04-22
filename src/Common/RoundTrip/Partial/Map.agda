module Common.RoundTrip.Partial.Map where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Prelude.Path
open import Prelude.Monoidal.Product.Indexed
open import Common.RoundTrip.Partial.Definition
open import Common.RoundTrip.Partial.Result

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
  map {B = B} f (roundTripPartial there1 back again1) = roundTripPartial there2 back again2
    where
      open Π
      there2 = mapUndefined f ∘ there1

      open ≡
      again2
        : (x : B)
        → there2 (back x) ≡ defined x
      again2 x = mapUndefined f · again1 x
