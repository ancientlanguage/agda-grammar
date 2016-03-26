module Common.RoundTripTransitive where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Prelude.Path
open import Prelude.Monoidal.Product.Indexed
open import Common.RoundTrip

open ≡

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
  (equiv A→B B→A pab)
  (equiv B→C C→B pbc)
  = equiv A→C C→A pac
  where
    A→C : A → C
    A→C = B→C Π.∘ A→B

    C→A : C → A
    C→A = B→A Π.∘ C→B

    pac
      : (c : C)
      → c ≡ B→C (A→B (B→A (C→B c)))
    pac c = pl ⟓ pr
      where
      pl : c ≡ B→C (C→B c)
      pl = pbc c

      paux : C→B c ≡ A→B (B→A (C→B c))
      paux = pab (C→B c)

      pr : B→C (C→B c) ≡ B→C (A→B (B→A (C→B c)))
      pr = B→C · paux

module ⟳ where
  _∘_ = roundTripTransitive
