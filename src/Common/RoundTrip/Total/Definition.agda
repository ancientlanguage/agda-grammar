module Common.RoundTrip.Total.Definition where

open import Agda.Primitive
open import Agda.Builtin.Equality

record RoundTrip
  {la lb : Level}
  (A : Set la)
  (B : Set lb)
  : Set (la ⊔ lb) where
  constructor roundTrip
  field
    there : A → B
    back : B → A
    again
      : (x : B)
      → there (back x) ≡ x

_⟳_ = RoundTrip
