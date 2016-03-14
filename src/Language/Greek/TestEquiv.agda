module Language.Greek.TestEquiv where

open import Agda.Builtin.Equality
open import Prelude.Product
open import Prelude.Sum
open import Common.EquivSum
open import Language.Greek.Concrete renaming (Letter to ConcreteLetter)
open import Language.Greek.Abstract renaming (Letter to AbstractLetter)
open import Language.Greek.AbstractConcrete
open import Language.Greek.ConcreteCombined

myEquiv
  : (x : Either ConcreteLetter Mark)
  → Σ (Either ConcreteLetter Mark → Either ComboEx Mark) λ f′ →
    Σ (Either ComboEx Mark → Either ConcreteLetter Mark) λ fInv′ →
    (x ≡ fInv′ (f′ x))
myEquiv = equivSumLeft abstractLetter abstractLetterInv abstractLetterEquiv

--testEquiv
--  : (c : Combined)
--  → (c ≡ 
