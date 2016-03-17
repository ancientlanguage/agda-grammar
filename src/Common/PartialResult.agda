module Common.PartialResult where

open import Agda.Primitive
open import Agda.Builtin.Unit
open import Prelude.Empty
open import Common.Sum

data PartialResult
  {ℓ₁ ℓ₂ : Level}
  (A : Set ℓ₁)
  (B : Set ℓ₂)
  : Set (ℓ₁ ⊔ ℓ₂)
  where
  defined : B → PartialResult A B
  undefined : A → PartialResult A B

Defined?
  : {ℓ₁ ℓ₂ : Level}
  → {A : Set ℓ₁}
  → {B : Set ℓ₂}
  → PartialResult A B
  → Set
Defined? (defined x) = ⊤
Defined? (undefined x) = ⊥

extractDefined
  : {ℓ₁ ℓ₂ : Level}
  → {A : Set ℓ₁}
  → {B : Set ℓ₂}
  → (x : PartialResult A B)
  → {_ : Defined? x}
  → B
extractDefined (defined x) = x
extractDefined (undefined x) {}
