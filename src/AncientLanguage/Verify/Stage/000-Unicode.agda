module AncientLanguage.Verify.Stage.000-Unicode where

open import AncientLanguage.Abstraction
open import AncientLanguage.Verify.Prepare
open import AncientLanguage.PrimarySource.Greek.Sblgnt
open import Agda.Builtin.String
open import AncientLanguage.Grammar.Greek.Script.Symbol
open import AncientLanguage.Grammar.Greek.Script.Mark
open import AncientLanguage.Grammar.Greek.Script.Unicode-Symbol

input : Fwd ∘ SourceWords $ String × EndSentence
input = prepareGroup sblgnt 

output : Fwd ∘ SourceWords $ (Fwd $ Symbol + Mark) × EndSentence
output = CP.asInr ((sourceWordsPath ∘ fst) fromString input)
  where open TraverseInr
