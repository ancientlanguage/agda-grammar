module AncientLanguage.Verify.Greek.Stage.Stage002.Output where

open import AncientLanguage.Verify.Greek.Stage.Stage002.To
import AncientLanguage.Verify.Greek.Stage.Stage001.Output as Previous

output : AllWords ((Fwd (LetterCaseFinalRecord × Fwd Mark)) × EndSentence)
output = Sum.asInr (to/error Previous.output)

