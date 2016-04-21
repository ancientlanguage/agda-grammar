module Language.Greek.Pipeline where

open import Agda.Primitive
open import Agda.Builtin.Char
open import Agda.Builtin.Equality
open import Prelude.Monoidal.Coproduct
open import Prelude.Monoidal.Product
open import Common.RoundTrip
open import Common.RoundTripProduct
open import Common.RoundTripSum
open import Common.RoundTripReflexive
open import Common.RoundTripTransitive
open import Common.RoundTripPartial
open import Common.RoundTripPartialLift
open import Common.RoundTripPartialMap
open import Common.RoundTripPartialReflexive
open import Common.RoundTripPartialTransitive
open import Language.Greek.Script
open import Language.Greek.AbstractConcrete
open import Language.Greek.Unicode

rt1 : Char ↻ LetterCaseFinal ⊕ Mark // NonGreekChar
rt1 = Char↻Symbol⊕Mark ↻.∘↑ (⟳.mapLeft Symbol⟳LetterCaseFinal)

{-
p1
  : {le la : Level}
  → {E : Set le}
  → {A : Set la}
  → (Char → E)
  → RoundTripP E (Char ⊗ A) ((LetterCaseFinal ⊕ Mark) ⊗ A)
p1 f = rtMapProduct (rtMapE f rt1) rtRefl
-}
