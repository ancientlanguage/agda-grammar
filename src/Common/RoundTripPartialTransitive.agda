module Common.RoundTripPartialTransitive where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Prelude.Equality
open import Prelude.Function
open import Common.RoundTripPartial
open import Common.PartialResult

transitiveRTP :
  {la lb lc le : Level}
  → {A : Set la}
  → {B : Set lb}
  → {C : Set lc}
  → {E : Set le}
  → A ↻ B ⁇ E
  → B ↻ C ⁇ E
  → A ↻ C ⁇ E
transitiveRTP {A = A} {B = B} {C = C} {E = E} (equiv A→B⁇E B→A pab) (equiv B→C⁇E C→B pbc) = equiv A→C⁇E C→A pac
  where
    A→C⁇E : A → C ⁇ E
    A→C⁇E = joinDefined A→B⁇E B→C⁇E

    C→A : C → A
    C→A = B→A ∘ C→B

    pac : (c : C) → defined c ≡ A→C⁇E (B→A (C→B c))
    pac c with cong (joinDefinedAux B→C⁇E) (pab (C→B c))
    … | r rewrite sym (pbc c) = r

_⊕⁇_ = transitiveRTP
