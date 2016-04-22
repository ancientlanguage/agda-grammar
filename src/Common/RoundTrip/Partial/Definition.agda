module Common.RoundTrip.Partial.Definition where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Common.RoundTrip.Partial.Result

record RoundTripPartial
  {le la lb : Level}
  (E : Set le)
  (A : Set la)
  (B : Set lb)
  : Set (le ⊔ la ⊔ lb) where
  constructor roundTripPartial
  field
    there : A → B ⁇ E
    back : B → A
    again
      : (x : B)
      → there (back x) ≡ defined x

syntax RoundTripPartial E A B = A ↻ B // E
