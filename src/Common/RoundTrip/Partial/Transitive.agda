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
  (roundTripPartial A→B⁇E B→A pab)
  (roundTripPartial B→C⁇E C→B pbc)
  = roundTripPartial A→C⁇E C→A pac
  where
    open ≡
    open Π

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
