module Language.Greek.Pipeline where

open import Agda.Primitive
open import Agda.Builtin.Char
open import Agda.Builtin.Equality
open import Prelude.Monoidal.Coproduct
open import Prelude.Monoidal.Product
open import Common.RoundTrip.Total.Definition
open import Common.RoundTrip.Total.Product
open import Common.RoundTrip.Total.Sum
open import Common.RoundTrip.Total.Reflexive
open import Common.RoundTrip.Total.Transitive
open import Common.RoundTrip.Partial.Definition
open import Common.RoundTrip.Partial.Lift
open import Common.RoundTrip.Partial.Map
open import Common.RoundTrip.Partial.Reflexive
open import Common.RoundTrip.Partial.Transitive
open import Language.Greek.Script
open import Language.Greek.SymbolLetter
open import Language.Greek.Unicode

rt1 : Char ↻ LetterCaseFinal ⊕ Mark // NonGreekChar
rt1 = Char↻Symbol⊕Mark ↻.∘↑ (⟳⊕.mapLeft Symbol⟳LetterCaseFinal)

{-
p1
  : {le la : Level}
  → {E : Set le}
  → {A : Set la}
  → (Char → E)
  → RoundTripP E (Char ⊗ A) ((LetterCaseFinal ⊕ Mark) ⊗ A)
p1 f = rtMapProduct (rtMapE f rt1) rtRefl
-}
