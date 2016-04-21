module Common.RoundTrip.Total.Transitive where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Prelude.Path
open import Prelude.Monoidal.Product.Indexed
open import Common.RoundTrip.Total.Definition

roundTripTransitive
  : {la lb lc : Level}
  → {A : Set la}
  → {B : Set lb}
  → {C : Set lc}
  → A ⟳ B
  → B ⟳ C
  → A ⟳ C
roundTripTransitive
  {A = A}
  {B = B}
  {C = C}
  (roundTrip there1 back1 again1)
  (roundTrip there2 back2 again2)
  = roundTrip there back again
  where
    there : A → C
    there = there2 Π.∘ there1

    back : C → A
    back = back1 Π.∘ back2

    again
      : (x : C)
      → there (back x) ≡ x
    again c = expanded
      where
      embed-back2 : there1 (back1 (back2 c)) ≡ back2 c
      embed-back2 = again1 (back2 c)

      left : there2 (there1 (back1 (back2 c))) ≡ there2 (back2 c)
      left = there2 ≡.· embed-back2

      right : there2 (back2 c) ≡ c
      right = again2 c

      expanded : there2 (there1 (back1 (back2 c))) ≡ c
      expanded = left ≡.⟓ right

_⟳∘_ = roundTripTransitive
