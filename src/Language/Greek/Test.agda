module Language.Greek.Test where

open import Agda.Builtin.Char
open import Prelude.Function
open import Language.Greek.Concrete
open import Language.Greek.Unicode

validCombined : Combined
validCombined = extractCombined ∘ concreteCombined $ 'α'
