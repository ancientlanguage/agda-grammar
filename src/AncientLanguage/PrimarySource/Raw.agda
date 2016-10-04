module AncientLanguage.PrimarySource.Raw where

open import Agda.Builtin.String
open import AncientLanguage.Common
open import AncientLanguage.PrimarySource using (Content; Source; milestone; word)

rawContent : Content → List String
rawContent (milestone _) = []
rawContent (word (word _ t _)) = t ∷ []

raw : Source → List String
raw s = List.joinMap rawContent (Source.getContents s)
