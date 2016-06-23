module Greek.Path where

open import Core
open import Greek.Script
open import Agda.Builtin.List
open Inhabit
open Sum

only-punctuation
  : (xs : List ((Concrete.Letter ⊕ Mark) ⊕ Punctuation))
  → {p : [ Which.inj2? (Assert.assert-inj2 xs) ]}
  → List Punctuation
only-punctuation xs {p} with Assert.assert-inj2 xs
… | inj1 a = from-⊥ p
… | inj2 b = b
