module Language.Greek.Test where

open import Agda.Builtin.Char
open import Prelude.Monoidal.Coproduct
open import Prelude.Monoidal.Void
open import Common.PartialResult
open import Language.Greek.Concrete
open import Language.Greek.Unicode

valid : Letter ⊕ Mark
valid = extractDefined (fromChar 'α')

-- invalid : Letter ⊕ Mark
-- invalid = extractDefined (fromChar 'Q')
