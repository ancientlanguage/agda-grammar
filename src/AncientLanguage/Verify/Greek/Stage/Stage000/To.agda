module AncientLanguage.Verify.Greek.Stage.Stage000.To where

open import AncientLanguage.Abstraction
open import AncientLanguage.Verify.Prepare
open import AncientLanguage.Grammar.Greek.Script
import AncientLanguage.Grammar.Greek.Script.Unicode-Symbol as Unicode-Symbol
open import Agda.Builtin.Char
open import Agda.Builtin.String

to/error
  : AllWords $ String × EndSentence
  → Fwd (Milestone × (String × EndSentence) × Char) + (AllWords $ (Fwd $ Symbol + Mark) × EndSentence)
to/error = (allWordsPath ∘ fst) Unicode-Symbol.stringToSymbol
  where
  open TraverseInr

to
  : (x : AllWords $ String × EndSentence)
  → {p : Sum.inrSet (to/error x)}
  → AllWords $ (Fwd $ Symbol + Mark) × EndSentence
to x {p} = Sum.asInr (to/error x) {p}
