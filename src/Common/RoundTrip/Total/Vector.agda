module Common.RoundTrip.Total.Vector where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Agda.Builtin.Size
open import Prelude.Natural
open import Prelude.Path
open import Prelude.Vector
open import Common.RoundTrip.Total.Definition

module ⟳Vec where
  map
    : {la lb : Level}
    → {n : Nat}
    → {A : Set la}
    → {B : Set lb}
    → A ⟳ B
    → Vec A n ⟳ Vec B n
  map
    {n = n}
    {A = A}
    {B = B}
    (roundTrip there back again)
    = roundTrip thereV backV againV
    where
      thereV
        : {s : Size}
        → {m : Nat}
        → Vec {s = s} A m
        → Vec {s = s} B m
      thereV = Vec.map there

      backV
        : {s : Size}
        → {m : Nat}
        → Vec {s = s} B m
        → Vec {s = s} A m
      backV = Vec.map back

      againV
        : {s : Size}
        → {m : Nat}
        → (x : Vec {s = s} B m)
        → thereV (backV x) ≡ x
      againV [] = refl
      againV (x ∷ xs) rewrite again x | againV xs = refl
