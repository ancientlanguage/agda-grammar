module Common.RoundTripPartialMap where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Prelude.Path
open import Prelude.Monoidal.Product.Indexed
open import Common.RoundTripPartial
open import Common.PartialResult

open Π
open ≡

rtMapE :
  {la lb le1 le2 : Level}
  → {A : Set la}
  → {B : Set lb}
  → {E1 : Set le1}
  → {E2 : Set le2}
  → (E1 → E2)
  → RoundTripP E1 A B
  → RoundTripP E2 A B
rtMapE {B = B} f (roundTripP A→B⁇E1 B→A p) = roundTripP A→B⁇E2 B→A q
  where
    A→B⁇E2 = mapUndefined f ∘ A→B⁇E1

    q : (x : B) → defined x ≡ A→B⁇E2 (B→A x)
    q x = mapUndefined f · p x
