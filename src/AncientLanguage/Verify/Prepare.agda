module AncientLanguage.Verify.Prepare where

open import Agda.Builtin.Char
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

data EndSentence : Set where
  end-sentence not-end-sentence : EndSentence

RawWord : Set → Set
RawWord X = X × EndSentence
Word : Set → Set
Word X = Marker × RawWord X
Source : Set → Set
Source X = GroupSourceId × X
SourceWords : Set → Set
SourceWords X = Source (List (Word X))

rawWords : {X : Set} → SourceWords X → Source (List (RawWord X))
rawWords sw = (Over.travSnd ∘ Over.travList) _×_.snd sw

suffixEndSentence : String → EndSentence
suffixEndSentence x = go not-end-sentence $ primStringToList x
  where
  go : EndSentence → List Char → EndSentence
  go s [] = s
  go s ('.' ∷ xs) = end-sentence
  go s (';' ∷ xs) = end-sentence
  go s (_ ∷ xs) = go s xs

prepareContents : List PS.Content → List (Word String)
prepareContents = go emptyMarker
  where
  open Traverse
  go : Marker → List PS.Content → List (Word String)
  go m [] = []
  go m (PS.milestone (PS.verse x) ∷ xs) = go (Over.travFst (const (some x)) m) xs 
  go m (PS.milestone PS.paragraph ∷ xs) = go (Over.travSnd next¶ m) xs 
  go m (PS.word (PS.word p t s) ∷ xs) = (m , t , suffixEndSentence s) ∷ go m xs

prepareSource : String → PS.Source → SourceWords String
prepareSource groupId s = groupSourceId groupId (PS.Source.getId s) , prepareContents (PS.Source.getContents s)

prepareGroup : PS.Group → List (SourceWords String)
prepareGroup g = List.map (prepareSource (PS.Group.getId g)) (PS.Group.getSources g)
