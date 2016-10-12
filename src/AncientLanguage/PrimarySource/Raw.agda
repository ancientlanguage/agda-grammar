{-# OPTIONS --no-eta-equality #-}

module AncientLanguage.PrimarySource.Raw where

open import Agda.Builtin.String
open import AncientLanguage.Abstraction
import AncientLanguage.PrimarySource as PS

rawContent : PS.Content → Fwd String
rawContent (PS.milestone _) = []
rawContent (PS.word (PS.word _ t _)) = t :> []

raw : PS.Source → Fwd String
raw s = Fwd.joinMap rawContent (PS.Source.getContents s)
