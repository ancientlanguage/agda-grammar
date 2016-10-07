{-# OPTIONS --no-eta-equality #-}

module AncientLanguage.PrimarySource.Raw where

open import Agda.Builtin.String
open import AncientLanguage.Common
import AncientLanguage.PrimarySource as PS

rawContent : PS.Content → List String
rawContent (PS.milestone _) = []
rawContent (PS.word (PS.word _ t _)) = t ∷ []

raw : PS.Source → List String
raw s = List.joinMap rawContent (PS.Source.getContents s)
