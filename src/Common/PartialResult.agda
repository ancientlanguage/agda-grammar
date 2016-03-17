module Common.PartialResult where

open import Agda.Primitive
open import Agda.Builtin.Unit
open import Prelude.Empty
open import Common.Sum

infixl 1 _⁇_

data _⁇_
  {la le : Level}
  (A : Set la)
  (E : Set le)
  : Set (la ⊔ le)
  where
  defined : A → A ⁇ E
  undefined : E → A ⁇ E

Defined?
  : {la le : Level}
  → {A : Set la}
  → {E : Set le}
  → A ⁇ E
  → Set
Defined? (defined x) = ⊤
Defined? (undefined x) = ⊥

extractDefined
  : {la le : Level}
  → {A : Set la}
  → {E : Set le}
  → (x : A ⁇ E)
  → {_ : Defined? x}
  → A
extractDefined (defined x) = x
extractDefined (undefined x) {}
