module AncientLanguage.PrimarySource.Raw where

open import Agda.Builtin.String
open import AncientLanguage.Common
import AncientLanguage.PrimarySource as PS

rawContent : PS.Content → List String
rawContent (PS.milestone _) = []
rawContent (PS.word (PS.word _ t _)) = t ∷ []

raw : PS.Source → List String
raw s = List.joinMap rawContent (PS.Source.getContents s)

data Paragraph : Set where
  start¶ : Paragraph
  end¶ : Paragraph
  mid¶ : Paragraph
  start-end¶ : Paragraph

data Milestone : Set where
  verse : PS.Verse → Milestone
  paragraph : Paragraph → Milestone

record Word : Set where
  constructor word
  field
    getPrefix : String
    getText : String
    getSuffix : String
    getMilestone : List Milestone

record OutSource : Set where
  field
    getGroup : PS.Group
    getSource : PS.Source
    getWords : List Word
