module Common.RoundTripProduct where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Prelude.Monoidal.Product
open import Prelude.Monoidal.Exponential
open import Prelude.Path
open import Common.RoundTrip
open import Common.RoundTripReflexive

open ≡ using (_·_)
open ⊗

rtMapProduct
  : {la lx lb ly : Level}
  → {A : Set la}
  → {X : Set lx}
  → {B : Set lb}
  → {Y : Set ly}
  → RoundTrip A X
  → RoundTrip B Y
  → RoundTrip (A ⊗ B) (X ⊗ Y)
rtMapProduct
  {A = A}
  {X = X}
  {B = B}
  {Y = Y}
  (roundTrip A→X X→A p)
  (roundTrip B→Y Y→B q)
  = roundTrip ab→xy xy→ab r
  where
    ab→xy = ⟨_⊗_⟩ A→X B→Y
    xy→ab = ⟨_⊗_⟩ X→A Y→B

    r : (xy : X ⊗ Y) → xy ≡ ab→xy (xy→ab xy)
    r (fst , snd) with p fst | q snd
    … | p1 | p2 rewrite ≡.inv p1 | ≡.inv p2 = refl
