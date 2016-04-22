module Common.RoundTrip.Partial.Transitive where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Prelude.Path
open import Prelude.Monoidal.Product.Indexed
open import Common.RoundTrip.Partial.Definition
open import Common.RoundTrip.Partial.Result

transitive :
  {la lb lc le : Level}
  → {A : Set la}
  → {B : Set lb}
  → {C : Set lc}
  → {E : Set le}
  → A ↻ B // E
  → B ↻ C // E
  → A ↻ C // E
transitive
  {A = A}
  {B = B}
  {C = C}
  {E = E}
  (roundTripPartial there1 back1 again1)
  (roundTripPartial there2 back2 again2)
  = roundTripPartial there back again
  where
    open ≡
    open Π

    there2↑ : B ⁇ E → C ⁇ E
    there2↑ = liftDomain there2

    there : A → C ⁇ E
    there = there2↑ ∘ there1

    back : C → A
    back = back1 ∘ back2

    again
      : (x : C)
      → there (back x) ≡ defined x
    again x = left ≡.⟓ right
      where
      aux : there1 (back1 (back2 x)) ≡ defined (back2 x)
      aux = again1 (back2 x)

      left : there2↑ (there1 (back1 (back2 x))) ≡ there2 (back2 x)
      left = there2↑ · aux

      right : there2 (back2 x) ≡ defined x
      right = again2 x

module ↻ where
  _∘_ = transitive

  open import Common.RoundTrip.Total.Definition
  open import Common.RoundTrip.Partial.Lift
  _∘↑_ :
    {la lb lc le : Level}
    → {A : Set la}
    → {B : Set lb}
    → {C : Set lc}
    → {E : Set le}
    → A ↻ B // E
    → B ⟳ C
    → A ↻ C // E
  _∘↑_ x y = transitive x (lift y)
