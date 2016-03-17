module Common.RoundTrip where

open import Agda.Primitive
open import Agda.Builtin.Equality

infixl 0 _⟳_

record _⟳_
  {la lb : Level}
  (A : Set la)
  (B : Set lb)
  : Set (la ⊔ lb) where
  constructor equiv
  field
    A→B : A → B
    B→A : B → A
    p : (x : B) → x ≡ A→B (B→A x)
