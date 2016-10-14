module AncientLanguage.Verify.Greek.Stage.Stage001.Output where

open import AncientLanguage.Abstraction
open import AncientLanguage.Verify.Prepare
open import AncientLanguage.Grammar.Greek.Script
open import AncientLanguage.Verify.Greek.Stage.Stage001.To
import AncientLanguage.Grammar.Greek.Script.Symbol-Letter as Symbol-Letter
import AncientLanguage.Verify.Greek.Stage.Stage000.Output as Previous

output : Fwd ∘ SourceWords $ (Fwd $ LetterCaseFinalRecord + Mark) × EndSentence
output = to Previous.output
