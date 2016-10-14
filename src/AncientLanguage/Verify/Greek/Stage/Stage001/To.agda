module AncientLanguage.Verify.Greek.Stage.Stage001.To where

open import AncientLanguage.Abstraction
open import AncientLanguage.Verify.Prepare
open import AncientLanguage.Grammar.Greek.Script
import AncientLanguage.Grammar.Greek.Script.Symbol-Letter as Symbol-Letter

to
  : Fwd ∘ SourceWords $ (Fwd $ Symbol + Mark) × EndSentence
  → Fwd ∘ SourceWords $ (Fwd $ LetterCaseFinalRecord + Mark) × EndSentence
to = (allWordsPathId ∘ fst ∘ fwd ∘ inl) Symbol-Letter.to
  where
  open TraverseId
