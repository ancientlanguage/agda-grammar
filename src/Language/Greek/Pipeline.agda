module Language.Greek.Pipeline where

open import Agda.Builtin.Char
open import Prelude.Monoidal.Coproduct
open import Common.RoundTrip.Partial.Definition
open import Common.RoundTrip.Partial.Transitive
open import Common.RoundTrip.Total.Sum
open import Language.Greek.Script
open import Language.Greek.SymbolLetter
open import Language.Greek.Unicode

stage1 : Char ↻ LetterCaseFinal ⊕ Mark // NonGreekChar
stage1 = Char↻Symbol⊕Mark ↻.∘↑ (⟳⊕.mapLeft Symbol⟳LetterCaseFinal)
