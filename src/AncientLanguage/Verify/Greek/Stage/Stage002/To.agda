module AncientLanguage.Verify.Greek.Stage.Stage002.To where

open import AncientLanguage.Abstraction
open import AncientLanguage.Verify.Prepare
open import AncientLanguage.Grammar.Greek.Script
import AncientLanguage.Grammar.Greek.Script.GroupMarks as GroupMarks

to/error
  : AllWords $ (Fwd $ LetterCaseFinalRecord + Mark) × EndSentence
  → Fwd
      ( Milestone
      × (Fwd (LetterCaseFinalRecord + Mark) × EndSentence)
      × GroupMarks.Error)
    + (AllWords ((Fwd (LetterCaseFinalRecord × Fwd Mark)) × EndSentence))
to/error = (allWordsPath ∘ fst) GroupMarks.to
  where
  open TraverseInr
