module Common.EquivCompose where

open import Agda.Primitive
open import Prelude.Equality
open import Prelude.Function
open import Common.Equiv

transEquiv
  : {ℓ₁ ℓ₂ ℓ₃ : Level}
  → {A : Set ℓ₁}
  → {B : Set ℓ₂}
  → {C : Set ℓ₃}
  → Equiv A B
  → Equiv B C
  → Equiv A C
transEquiv {A = A} {B = B} {C = C} (equiv f f⁻¹ p) (equiv g g⁻¹ q) = equiv gf f⁻¹g⁻¹ r
  where
    gf = g ∘ f
    f⁻¹g⁻¹ = f⁻¹ ∘ g⁻¹

    r : (x : C) → x ≡ g (f (f⁻¹ (g⁻¹ x)))
    r x with p (g⁻¹ x) | q x
    … | rp | rq with cong g rp
    … | rc rewrite (sym rq) = rc

_-[]-_ = transEquiv
