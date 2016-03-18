module Common.RoundTripTransitive where

open import Agda.Primitive
open import Prelude.Equality
open import Prelude.Function
open import Common.RoundTrip

roundTripTransitive
  : {la lb lc : Level}
  → {A : Set la}
  → {B : Set lb}
  → {C : Set lc}
  → A ⟳ B
  → B ⟳ C
  → A ⟳ C
roundTripTransitive {C = C} (equiv A→B B→A pab) (equiv B→C C→B pbc) = equiv A→C C→A pac
  where
    A→C = B→C ∘ A→B
    C→A = B→A ∘ C→B

    pac : (c : C) → c ≡ B→C (A→B (B→A (C→B c)))
    pac c with cong B→C (pab (C→B c))
    … | r rewrite sym (pbc c) = r

_⊕_ = roundTripTransitive
