module Common.RoundTripSum where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Prelude.Monoidal.Coproduct
open import Prelude.Monoidal.Exponential
open import Prelude.Path
open import Common.RoundTrip
open import Common.RoundTripReflexive

open ⊕

module ⟳⊕ where
  mapBoth
    : {la lx lb ly : Level}
    → {A : Set la}
    → {X : Set lx}
    → {B : Set lb}
    → {Y : Set ly}
    → A ⟳ X
    → B ⟳ Y
    → (A ⊕ B) ⟳ (X ⊕ Y)
  mapBoth
    {A = A}
    {X = X}
    {B = B}
    {Y = Y}
    (roundTrip A→X X→A p)
    (roundTrip B→Y Y→B q)
    = roundTrip ab→xy xy→ab r
    where
      ab→xy = [ A→X ⊕ B→Y ]
      xy→ab = [ X→A ⊕ Y→B ]

      r : (xy : X ⊕ Y)
        → xy ≡ ab→xy (xy→ab xy)
      r (inl x) = inl ≡.· p x
      r (inr y) = inr ≡.· q y

  mapLeft
    : {la lx lb : Level}
    → {A : Set la}
    → {X : Set lx}
    → {B : Set lb}
    → A ⟳ X
    → (A ⊕ B) ⟳ (X ⊕ B)
  mapLeft f = mapBoth f ⟳.reflexivity

  mapRight
    : {la lb ly : Level}
    → {A : Set la}
    → {B : Set lb}
    → {Y : Set ly}
    → B ⟳ Y
    → (A ⊕ B) ⟳ (A ⊕ Y)
  mapRight f = mapBoth ⟳.reflexivity f
