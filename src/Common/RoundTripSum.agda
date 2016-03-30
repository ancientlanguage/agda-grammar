module Common.RoundTripSum where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Prelude.Monoidal.Coproduct
open import Prelude.Monoidal.Exponential.Boot
open import Prelude.Path
open import Common.RoundTrip

open ≡ using (_·_)
open ⊕

roundTripSumMap
  : {la lx lb ly : Level}
  → {A : Set la}
  → {X : Set lx}
  → {B : Set lb}
  → {Y : Set ly}
  → A ⟳ X
  → B ⟳ Y
  → A ⊕ B ⟳ X ⊕ Y
roundTripSumMap {A = A} {X = X} {B = B} {Y = Y} (equiv A→X X→A p) (equiv B→Y Y→B q) = equiv ab→xy xy→ab r
  where
    ab→xy = [_⊕_] A→X B→Y
    xy→ab = [_⊕_] X→A Y→B
    r : (xy : X ⊕ Y) → xy ≡ ab→xy (xy→ab xy)
    r (inl x) = inl · p x
    r (inr y) = inr · q y
