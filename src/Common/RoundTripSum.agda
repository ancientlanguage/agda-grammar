module Common.RoundTripSum where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Prelude.Path
open import Common.RoundTrip
open import Common.Sum

open ≡

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

roundTripSumLeft
  : {ℓ₁ ℓ₁′ ℓ₂ : Level}
  → {A : Set ℓ₁}
  → {A′ : Set ℓ₁′}
  → {B : Set ℓ₂}
  → A ⟳ A′
  → (A ⊎ B) ⟳ (A′ ⊎ B)
roundTripSumLeft {A = A} {A′ = A′} {B = B} (equiv f f⁻¹ p) = equiv g g⁻¹ q
  where
    g = mapLeft f
    g⁻¹ = mapLeft f⁻¹

    q :  (b : A′ ⊎ B) → b ≡ g (g⁻¹ b)
    q (left x) = left · p x
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

roundTripSumRight
  : {ℓ₁ ℓ₂ ℓ₂′ : Level}
  → {A : Set ℓ₁}
  → {B : Set ℓ₂}
  → {B′ : Set ℓ₂′}
  → B ⟳ B′
  → (A ⊎ B) ⟳ (A ⊎ B′)
roundTripSumRight {A = A} {B = B} {B′ = B′} (equiv A→B B→A p) = equiv A⊎B→A⊎B′ A⊎B′→A⊎B q
  where
    A⊎B→A⊎B′ = mapRight A→B
    A⊎B′→A⊎B = mapRight B→A

    q : (b : A ⊎ B′) → b ≡ A⊎B→A⊎B′ (A⊎B′→A⊎B b)
    q (left x) = refl
    q (right y) = right · p y
