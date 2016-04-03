module Language.Greek.Pipeline where

open import Agda.Builtin.Char
open import Agda.Builtin.Equality
open import Prelude.Monoidal.Coproduct
open import Common.RoundTrip
open import Common.RoundTripSum
open import Common.RoundTripReflexive
open import Common.RoundTripTransitive
open import Common.RoundTripPartial
open import Common.RoundTripPartialLift
open import Common.RoundTripPartialReflexive
open import Common.RoundTripPartialTransitive
open import Language.Greek.Concrete
open import Language.Greek.Abstract
open import Language.Greek.AbstractConcrete
open import Language.Greek.Unicode

pipeline : RoundTripP Char Char (LetterCaseFinal ⊕ Mark)
pipeline = Char↻Letter⊕Mark ↻∘ lift (rtMapLeft ConcreteLetter⟳LetterCaseFinal)
