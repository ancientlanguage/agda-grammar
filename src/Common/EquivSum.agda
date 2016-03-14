module Common.EquivSum where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Prelude.Function
open import Prelude.Product
open import Prelude.Sum

equivSumLeft
  : {ℓ₁ : Level}
  → {ℓ₁′ : Level}
  → {ℓ₂ : Level}
  → {A : Set ℓ₁}
  → {A′ : Set ℓ₁′}
  → {B : Set ℓ₂}
  → (f : A → A′)
  → (fInv : A′ → A)
  → (p : (x : A′) → (x ≡ f (fInv x)))
  → (x : Either A B)
  → Σ (Either A B → Either A′ B) λ f′ →
    Σ (Either A′ B → Either A B) λ fInv′ →
    (x ≡ fInv′ (f′ x))
equivSumLeft f fInv p (left x) = const (left (f x)) , const (left x) , refl
equivSumLeft f fInv p (right x) = const (right x) , const (right x) , refl

equivSumRight
  : {ℓ₁ : Level}
  → {ℓ₂ : Level}
  → {ℓ₂′ : Level}
  → {A : Set ℓ₁}
  → {B : Set ℓ₂}
  → {B′ : Set ℓ₂′}
  → (f : B → B′)
  → (fInv : B′ → B)
  → (p : (x : B′) → (x ≡ f (fInv x)))
  → (x : Either A B)
  → Σ (Either A B → Either A B′) λ f′ →
    Σ (Either A B′ → Either A B) λ fInv′ →
    (x ≡ fInv′ (f′ x))
equivSumRight f fInv p (left x) = const (left x) , const (left x) , refl
equivSumRight f fInv p (right x) = const (right (f x)) , const (right x) , refl
