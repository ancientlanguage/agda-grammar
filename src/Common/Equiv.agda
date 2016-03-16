module Common.Equiv where

open import Agda.Primitive
open import Agda.Builtin.Equality

record Equiv
  {la lb : Level}
  (A : Set la)
  (B : Set lb)
  : Set (la ⊔ lb) where
  constructor equiv
  field
    f : A → B
    f⁻¹ : B → A
    p : (x : B) → x ≡ f (f⁻¹ x)
