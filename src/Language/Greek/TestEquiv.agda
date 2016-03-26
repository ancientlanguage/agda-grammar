module Language.Greek.TestEquiv where

open import Agda.Builtin.Equality
open import Prelude.Monoidal.Coproduct
open import Common.RoundTrip
open import Common.RoundTripSum
open import Common.RoundTripReflexive
open import Common.RoundTripTransitive
open import Language.Greek.Concrete renaming (Letter to ConcreteLetter)
open import Language.Greek.Abstract renaming (Letter to AbstractLetter)
open import Language.Greek.AbstractConcrete
open import Language.Greek.ConcreteCombined

testEquiv : Combined ⟳ Combo ⊕ Mark
testEquiv = letterOrMarkEquiv ⟳.∘ (roundTripSumMap abstractLetterEquiv roundTripReflexive)
