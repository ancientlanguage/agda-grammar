module Common.RoundTripPartial where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Common.PartialResult

record RoundTripP
  {le la lb : Level}
  (E : Set le)
  (A : Set la)
  (B : Set lb)
  : Set (le ⊔ la ⊔ lb) where
  constructor roundTripP
  field
    A→B⁇E : A → B ⁇ E
    B→A : B → A
    p : (x : B) → defined x ≡ A→B⁇E (B→A x)
