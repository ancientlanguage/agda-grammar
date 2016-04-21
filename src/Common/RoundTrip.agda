module Common.RoundTrip where

open import Agda.Primitive
open import Agda.Builtin.Equality

record RoundTrip
  {la lb : Level}
  (A : Set la)
  (B : Set lb)
  : Set (la ⊔ lb) where
  constructor roundTrip
  field
    A→B : A → B
    B→A : B → A
    p : (x : B) → x ≡ A→B (B→A x)

_⟳_ = RoundTrip
