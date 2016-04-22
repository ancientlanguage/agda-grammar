module Common.RoundTrip.Partial.Vector where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Agda.Builtin.Size
open import Prelude.Natural
open import Prelude.Path
open import Prelude.Vector
open import Prelude.Applicative
open import Common.RoundTrip.Partial.Definition
open import Common.RoundTrip.Partial.Result

traverse
  : {s : Size}
  → {le la lb : Level}
  → {E : Set le}
  → {A : Set la}
  → {B : Set lb}
  → {n : Nat}
  → (A → B ⁇ E)
  → Vec {s} A n
  → (Vec {s} B n) ⁇ E
traverse f [] = defined []
traverse f (x ∷ xs) with f x
… | undefined e = undefined e
… | defined b with traverse f xs
… | defined bs = defined (b ∷ bs)
… | undefined e = undefined e

module ⟳Vec where
  map
    : {le la lb : Level}
    → {n : Nat}
    → {E : Set le}
    → {A : Set la}
    → {B : Set lb}
    → A ↻ B // E
    → Vec A n ↻ Vec B n // E
  map
    {n = n}
    {E = E}
    {A = A}
    {B = B}
    (roundTripPartial there back again)
    = roundTripPartial thereV backV againV
    where
      thereV
        : {s : Size}
        → {m : Nat}
        → Vec {s = s} A m
        → Vec {s = s} B m ⁇ E
      thereV {s = s} = traverse {s = s} there

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
        → thereV (backV x) ≡ defined x
      againV [] = refl
      againV (x ∷ xs) rewrite again x | againV xs = refl
