module Language.Greek.TestEquiv where

open import Agda.Builtin.Equality
open import Prelude.Product
open import Common.Equiv
open import Common.EquivSum
open import Common.EquivCompose
open import Common.Sum
open import Language.Greek.Concrete renaming (Letter to ConcreteLetter)
open import Language.Greek.Abstract renaming (Letter to AbstractLetter)
open import Language.Greek.AbstractConcrete
open import Language.Greek.ConcreteCombined

testEquiv : Equiv Combined (Combo ⊎ Mark)
testEquiv = letterOrMarkEquiv -[]- (equivSumLeft abstractLetterEquiv)
