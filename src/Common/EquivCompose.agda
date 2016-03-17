module Common.EquivCompose where

open import Agda.Primitive
open import Prelude.Equality
open import Prelude.Function
open import Common.Equiv

transEquiv
  : {la lb lc : Level}
  → {A : Set la}
  → {B : Set lb}
  → {C : Set lc}
  → Equiv A B
  → Equiv B C
  → Equiv A C
transEquiv {C = C} (equiv f f⁻¹ p) (equiv g g⁻¹ q) = equiv gf f⁻¹g⁻¹ r
  where
    gf = g ∘ f
    f⁻¹g⁻¹ = f⁻¹ ∘ g⁻¹

    r : (x : C) → x ≡ g (f (f⁻¹ (g⁻¹ x)))
    r x with cong g (p (g⁻¹ x))
    … | s rewrite sym (q x) = s

_-[]-_ = transEquiv
