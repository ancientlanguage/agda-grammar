module AncientLanguage.Verify.Stage.000-Unicode where

open import AncientLanguage.Common
open import AncientLanguage.Verify.Prepare
open import AncientLanguage.PrimarySource.Greek.Sblgnt
open import Agda.Builtin.String
open import Agda.Builtin.Strict

sources : Fwd ∘ SourceWords $ String × EndSentence
sources = primForce sblgnt prepareGroup

eachWord : {A B : Set} → (A → B) → Fwd ∘ SourceWords $ A → Fwd ∘ SourceWords $ B
eachWord = Over.travFwd ∘ Over.travSnd ∘ Over.travFwd ∘ Over.travSnd
