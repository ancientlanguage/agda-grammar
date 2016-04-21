module Common.RoundTrip.Partial.Lift where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Prelude.Path
open import Prelude.Monoidal.Product.Indexed
open import Common.RoundTrip.Total.Definition
open import Common.RoundTrip.Partial.Definition
open import Common.RoundTrip.Partial.Result

lift
  : {le la lb : Level}
  → {E : Set le}
  → {A : Set la}
  → {B : Set lb}
  → A ⟳ B
  → A ↻ B // E
lift {A = A} {B = B} (roundTrip there back again) = roundTripPartial A→B⁇E back q
  where
    A→B⁇E = defined Π.∘ there

    q : (x : B) → defined x ≡ A→B⁇E (back x)
    q x rewrite again x = refl
