module AncientLanguage.Verify.Greek.Stage.Stage000.Output where

open import AncientLanguage.Abstraction
open import AncientLanguage.Verify.Prepare
open import AncientLanguage.PrimarySource.Greek.Sblgnt
open import AncientLanguage.Grammar.Greek.Script.Symbol
open import AncientLanguage.Grammar.Greek.Script.Mark
open import AncientLanguage.Grammar.Greek.Script.Unicode-Symbol
open import Agda.Builtin.Char
open import Agda.Builtin.String

input : Fwd ∘ SourceWords $ String × EndSentence
input = prepareGroup sblgnt

output-w/error : Fwd (Milestone × Char) + (Fwd ∘ SourceWords $ (Fwd $ Symbol + Mark) × EndSentence)
output-w/error = (sourceWordsPath ∘ fst) stringToSymbol input
  where
  open TraverseInr

output : Fwd ∘ SourceWords $ (Fwd $ Symbol + Mark) × EndSentence
output = CP.asInr output-w/error
