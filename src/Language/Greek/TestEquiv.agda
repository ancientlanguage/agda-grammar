module Language.Greek.TestEquiv where

open import Agda.Builtin.Equality
open import Prelude.Product
open import Common.EquivSum
open import Common.Sum
open import Language.Greek.Concrete renaming (Letter to ConcreteLetter)
open import Language.Greek.Abstract renaming (Letter to AbstractLetter)
open import Language.Greek.AbstractConcrete
open import Language.Greek.ConcreteCombined

myEquiv
  : (x : ConcreteLetter ⊎ Mark)
  → Σ (ConcreteLetter ⊎ Mark → ComboEx ⊎ Mark) λ f →
    Σ (ComboEx ⊎ Mark → ConcreteLetter ⊎ Mark) λ fInv →
    (x ≡ fInv (f x))
myEquiv = equivSumLeft abstractLetter abstractLetterInv abstractLetterEquiv

--testEquiv
--  : (c : Combined)
--  → (c ≡ 
