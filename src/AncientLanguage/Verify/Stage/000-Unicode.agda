module AncientLanguage.Verify.Stage.000-Unicode where

open import AncientLanguage.Abstraction
open import AncientLanguage.Verify.Prepare
open import AncientLanguage.PrimarySource.Greek.Sblgnt
open import Agda.Builtin.String
open import AncientLanguage.Grammar.Greek.Script.Symbol
open import AncientLanguage.Grammar.Greek.Script.Mark
import AncientLanguage.Grammar.Greek.Script.Unicode-Symbol

prepared-sources : Fwd ∘ SourceWords $ String × EndSentence
prepared-sources = prepareGroup sblgnt 

stage000-sources : Fwd ∘ SourceWords $ (Fwd $ Symbol + Mark) × EndSentence
stage000-sources = {!!}
