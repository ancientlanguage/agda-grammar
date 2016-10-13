module AncientLanguage.Verify.Greek.Stage.Stage000.Back where

open import AncientLanguage.Abstraction
open import AncientLanguage.Verify.Prepare
open import AncientLanguage.Grammar.Greek.Script.Unicode-Symbol
open import AncientLanguage.Verify.Greek.Stage.Stage000.Output

back : (sourceWordsPathId ∘ TraverseId.fst) toString output ≡ input
back = {!!} -- refl
