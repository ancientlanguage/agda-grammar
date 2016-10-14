module AncientLanguage.Verify.Greek.Stage.Stage000.Output where

open import AncientLanguage.Abstraction
open import AncientLanguage.Verify.Prepare
open import AncientLanguage.PrimarySource.Greek.Sblgnt
open import AncientLanguage.Grammar.Greek.Script
open import AncientLanguage.Verify.Greek.Stage.Stage000.To

output : AllWords $ (Fwd $ Symbol + Mark) × EndSentence
output = to (prepareGroup sblgnt)
