module Language.Greek.Common where

open import Agda.Primitive
open import Agda.Builtin.Unit
open import Prelude.Empty

data _PartialResultTo_
  {ℓ₁ : Level}
  {ℓ₂ : Level}
  (A : Set ℓ₁)
  (B : Set ℓ₂)
  : Set (ℓ₁ ⊔ ℓ₂)
  where
  defined : B → A PartialResultTo B
  undefined : A → A PartialResultTo B

defined?
  : {ℓ₁ : Level}
  → {ℓ₂ : Level}
  → {A : Set ℓ₁}
  → {B : Set ℓ₂}
  → A PartialResultTo B
  → Set
defined? (defined x) = ⊤
defined? (undefined x) = ⊥

extractDefined
  : {ℓ₁ : Level}
  → {ℓ₂ : Level}
  → {A : Set ℓ₁}
  → {B : Set ℓ₂}
  → (x : A PartialResultTo B)
  → {_ : defined? x}
  → B
extractDefined (defined x) = x
extractDefined (undefined x) {}

