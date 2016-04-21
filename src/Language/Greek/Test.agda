module Language.Greek.Test where

open import Agda.Builtin.Char
open import Prelude.Monoidal.Coproduct
open import Prelude.Monoidal.Void
open import Common.PartialResult
open import Language.Greek.Script
open import Language.Greek.Unicode

valid : Symbol ⊕ Mark
valid = extractDefined (fromChar 'α')

-- invalid : Symbol ⊕ Mark
-- invalid = extractDefined (fromChar 'Q')
