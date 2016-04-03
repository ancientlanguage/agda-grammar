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
open import Language.Greek.Concrete renaming (Letter to ConcreteLetter)
open import Language.Greek.Abstract renaming (Letter to AbstractLetter)
open import Language.Greek.AbstractConcrete
open import Language.Greek.ConcreteCombined
open import Language.Greek.Unicode

open ⟳ using (_∘_)

letter : Combined ⟳ LetterCaseFinal ⊕ Mark
letter = letterOrMarkEquiv ∘ roundTripSumMap abstractLetterEquiv roundTripReflexive

pipeline : Char ↻ (LetterCaseFinal ⊕ Mark) ⁇ Char
pipeline = concreteCombinedRoundTripPartial ∘⁇ lift letter
