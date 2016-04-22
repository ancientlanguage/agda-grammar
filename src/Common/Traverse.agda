module Common.Traverse where

open import Agda.Primitive
open import Agda.Builtin.Size
open import Prelude.Natural
open import Prelude.Vector
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
