module Common.RoundTripPartial where

open import Agda.Primitive
open import Agda.Builtin.Equality
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
