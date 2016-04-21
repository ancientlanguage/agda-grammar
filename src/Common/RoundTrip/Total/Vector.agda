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
    (roundTrip A→B B→A p)
    = roundTrip there back q
    where
      there
        : {s : Size}
        → {m : Nat}
        → Vec {s = s} A m
        → Vec {s = s} B m
      there = Vec.map A→B

      back
        : {s : Size}
        → {m : Nat}
        → Vec {s = s} B m
        → Vec {s = s} A m
      back = Vec.map B→A

      q : {s : Size}
        → {m : Nat}
        → (x : Vec {s = s} B m)
        → x ≡ there (back x)
      q [] = refl
      q (x ∷ xs) rewrite ≡.inv (p x) | ≡.inv (q xs) = refl
