module AncientLanguage.Verify.Greek.Stage.Stage002.Output where

open import AncientLanguage.Abstraction
open import AncientLanguage.Verify.Prepare
open import AncientLanguage.Grammar.Greek.Script
open import AncientLanguage.Verify.Greek.Stage.Stage002.To
import AncientLanguage.Verify.Greek.Stage.Stage001.Output as Previous

output : AllWords ((Fwd (LetterCaseFinalRecord × Fwd Mark)) × EndSentence)
output = Sum.asInr (to/error Previous.output)
