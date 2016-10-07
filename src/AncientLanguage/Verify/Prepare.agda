module AncientLanguage.Verify.Prepare where

open import Agda.Builtin.String
open import AncientLanguage.Common
import AncientLanguage.PrimarySource as PS

data ¶Num : Set where
  ¶num : Nat → ¶Num

Marker : Set
Marker = Maybe PS.Verse × Maybe ¶Num

next¶ : Maybe ¶Num → Maybe ¶Num
next¶ none = some (¶num zero)
next¶ (some (¶num p)) = some (¶num (suc p))

emptyMarker : Marker
emptyMarker = none , none

record GroupSourceId : Set where
  constructor groupSourceId
  field
    getGroupId : String
    getSourceId : String

WordString = Marker × String
Source = λ X → GroupSourceId × X

prepareContents : List PS.Content → List WordString
prepareContents = go emptyMarker
  where
  open Traverse
  go : Marker → List PS.Content → List WordString
  go m [] = []
  go m (PS.milestone (PS.verse x) ∷ xs) = go (Over.travFst (const (some x)) m) xs 
  go m (PS.milestone PS.paragraph ∷ xs) = go (Over.travSnd next¶ m) xs 
  go m (PS.word (PS.word p t s) ∷ xs) = (m , t) ∷ go m xs

prepareSource : String → PS.Source → Source (List WordString)
prepareSource groupId s = groupSourceId groupId (PS.Source.getId s) , prepareContents (PS.Source.getContents s)

prepareGroup : PS.Group → List (Source (List WordString))
prepareGroup g = List.map (prepareSource (PS.Group.getId g)) (PS.Group.getSources g)
