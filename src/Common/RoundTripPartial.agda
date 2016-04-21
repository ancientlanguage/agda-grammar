module Common.RoundTripPartial where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Common.PartialResult

record RoundTripPartial
  {le la lb : Level}
  (E : Set le)
  (A : Set la)
  (B : Set lb)
  : Set (le ⊔ la ⊔ lb) where
  constructor roundTripPartial
  field
    A→B⁇E : A → B ⁇ E
    B→A : B → A
    p : (x : B) → defined x ≡ A→B⁇E (B→A x)

syntax RoundTripPartial E A B = A ↻ B // E
