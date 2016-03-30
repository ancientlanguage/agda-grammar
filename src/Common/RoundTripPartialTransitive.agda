module Common.RoundTripPartialTransitive where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Prelude.Path
open import Prelude.Monoidal.Product.Indexed
open import Common.RoundTripPartial
open import Common.PartialResult

open ≡
open Π

transitiveRTP :
  {la lb lc le : Level}
  → {A : Set la}
  → {B : Set lb}
  → {C : Set lc}
  → {E : Set le}
  → A ↻ B ⁇ E
  → B ↻ C ⁇ E
  → A ↻ C ⁇ E
transitiveRTP
  {A = A}
  {B = B}
  {C = C}
  {E = E}
  (equiv A→B⁇E B→A pab)
  (equiv B→C⁇E C→B pbc)
  = equiv A→C⁇E C→A pac
  where
    B⁇E→C⁇E : B ⁇ E → C ⁇ E
    B⁇E→C⁇E = liftDomain B→C⁇E

    A→C⁇E : A → C ⁇ E
    A→C⁇E = B⁇E→C⁇E ∘ A→B⁇E 

    C→A : C → A
    C→A = B→A ∘ C→B

    pac
      : (c : C)
      → defined c ≡ A→C⁇E (B→A (C→B c))
    pac c = pl ≡.⟓ pr
      where
      pl : defined c ≡ B→C⁇E (C→B c)
      pl = pbc c

      paux : defined (C→B c) ≡ A→B⁇E (B→A (C→B c))
      paux = pab (C→B c)

      pr : B→C⁇E (C→B c) ≡ A→C⁇E (B→A (C→B c))
      pr = B⁇E→C⁇E · paux

_∘⁇_ = transitiveRTP
