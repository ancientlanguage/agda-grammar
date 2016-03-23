module Language.Greek.Test where

open import Agda.Builtin.Char
open import Prelude.Monoidal.Product.Indexed
open import Common.PartialResult
open import Language.Greek.Concrete
open import Language.Greek.Unicode

open Π

validCombined : Combined
validCombined = (extractDefined ∘ concreteCombined) 'α'

--invalidCombined : Combined
--invalidCombined = extractDefined ∘ concreteCombined $ 'Q'
