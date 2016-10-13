module AncientLanguage.Verify.Greek.Stage.Stage001 where

open import AncientLanguage.Abstraction
open import AncientLanguage.Verify.Prepare
open import AncientLanguage.Grammar.Greek.Script.Letter
open import AncientLanguage.Grammar.Greek.Script.Mark
import AncientLanguage.Grammar.Greek.Script.Symbol-Letter as Symbol-Letter
import AncientLanguage.Verify.Greek.Stage.Stage000.Output as Previous

output : Fwd ∘ SourceWords $ (Fwd $ LetterCaseFinalRecord + Mark) × EndSentence
output = (sourceWordsPathId ∘ fst ∘ fwd ∘ inl) Symbol-Letter.to Previous.output
  where
  open TraverseId
