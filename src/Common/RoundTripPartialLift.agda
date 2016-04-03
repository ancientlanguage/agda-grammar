module Common.RoundTripPartialLift where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Prelude.Path
open import Prelude.Monoidal.Product.Indexed
open import Common.RoundTrip
open import Common.RoundTripPartial
open import Common.PartialResult

lift
  : {la lb le : Level}
  → {A : Set la}
  → {B : Set lb}
  → {E : Set le}
  → RoundTrip A B
  → RoundTripP E A B
lift {A = A} {B = B} (roundTrip A→B B→A p) = roundTripP A→B⁇E B→A q
  where
    A→B⁇E = defined Π.∘ A→B

    q : (x : B) → defined x ≡ A→B⁇E (B→A x)
    q x = defined ≡.· p x
