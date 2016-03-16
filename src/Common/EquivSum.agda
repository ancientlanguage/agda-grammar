module Common.EquivSum where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Prelude.Equality
open import Prelude.Function
open import Prelude.Product
open import Common.Equiv
open import Common.Sum

mapLeft
  : {ℓ₁ ℓ₁′ ℓ₂ : Level}
  → {A : Set ℓ₁}
  → {A′ : Set ℓ₁′}
  → {B : Set ℓ₂}
  → (f : A → A′)
  → A ⊎ B
  → A′ ⊎ B
mapLeft f (left x) = left (f x)
mapLeft f (right y) = right y

equivSumLeft
  : {ℓ₁ ℓ₁′ ℓ₂ : Level}
  → {A : Set ℓ₁}
  → {A′ : Set ℓ₁′}
  → {B : Set ℓ₂}
  → Equiv A A′
  → Equiv (A ⊎ B) (A′ ⊎ B)
equivSumLeft {A = A} {A′ = A′} {B = B} (equiv f f⁻¹ p) = equiv g g⁻¹ q
  where
    g = mapLeft f
    g⁻¹ = mapLeft f⁻¹

    q :  (b : A′ ⊎ B) → b ≡ g (g⁻¹ b)
    q (left x) = cong left (p x)
    q (right y) = refl

mapRight
  : {ℓ₁ ℓ₂ ℓ₂′ : Level}
  → {A : Set ℓ₁}
  → {B : Set ℓ₂}
  → {B′ : Set ℓ₂′}
  → (f : B → B′)
  → A ⊎ B
  → A ⊎ B′
mapRight f (left x) = left x
mapRight f (right y) = right (f y)

equivSumRight
  : {ℓ₁ ℓ₂ ℓ₂′ : Level}
  → {A : Set ℓ₁}
  → {B : Set ℓ₂}
  → {B′ : Set ℓ₂′}
  → Equiv B B′
  → Equiv (A ⊎ B) (A ⊎ B′)
equivSumRight {A = A} {B = B} {B′ = B′} (equiv f f⁻¹ p) = equiv g g⁻¹ q
  where
    g = mapRight f
    g⁻¹ = mapRight f⁻¹

    q : (b : A ⊎ B′) → b ≡ g (g⁻¹ b)
    q (left x) = refl
    q (right y) = cong right (p y)
