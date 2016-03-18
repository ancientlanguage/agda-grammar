module Common.RoundTripPartial where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Prelude.Equality
open import Prelude.Function
open import Common.PartialResult

infixl 0 _↻_⁇_

record _↻_⁇_
  {la lb le : Level}
  (A : Set la)
  (B : Set lb)
  (E : Set le)
  : Set (la ⊔ lb ⊔ le) where
  constructor equiv
  field
    A→B⁇E : A → B ⁇ E
    B→A : B → A
    p : (x : B) → defined x ≡ A→B⁇E (B→A x)

mapE :
  {la lb le1 le2 : Level}
  → {A : Set la}
  → {B : Set lb}
  → {E1 : Set le1}
  → {E2 : Set le2}
  → (E1 → E2)
  → A ↻ B ⁇ E1
  → A ↻ B ⁇ E2
mapE {B = B} f (equiv A→B⁇E1 B→A p) = equiv A→B⁇E2 B→A q
  where
    A→B⁇E2 = mapUndefined f ∘ A→B⁇E1
    q : (x : B) → defined x ≡ A→B⁇E2 (B→A x)
    q x = cong (mapUndefined f) (p x)
