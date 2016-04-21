module Common.RoundTrip.Total.Sum where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Prelude.Monoidal.Coproduct
open import Prelude.Monoidal.Exponential
open import Prelude.Path
open import Common.RoundTrip.Total.Definition
open import Common.RoundTrip.Total.Reflexive

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
    (roundTrip thereLeft backLeft againLeft)
    (roundTrip thereRight backRight againRight)
    = roundTrip there back again
    where
      there = [ thereLeft ⊕ thereRight ]
      back = [ backLeft ⊕ backRight ]

      again
        : (x : X ⊕ Y)
        → there (back x) ≡ x
      again (inl x) = inl ≡.· againLeft x
      again (inr y) = inr ≡.· againRight y

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
