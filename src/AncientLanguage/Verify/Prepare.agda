module AncientLanguage.Verify.Prepare where

open import Agda.Builtin.Char
open import Agda.Builtin.String
open import AncientLanguage.Common
import AncientLanguage.PrimarySource as PS

data ¶Num : Set where
  ¶num : Nat → ¶Num

Milestone : Set
Milestone = Maybe PS.Verse × Maybe ¶Num

next¶ : Maybe ¶Num → Maybe ¶Num
next¶ none = some (¶num zero)
next¶ (some (¶num p)) = some (¶num (suc p))

emptyMilestone : Milestone
emptyMilestone = none , none

record SourceId : Set where
  constructor sourceId
  field
    getGroupId : String
    getSourceId : String

data EndSentence : Set where
  end-sentence not-end-sentence : EndSentence

Milestoned : Set → Set
Milestoned X = Milestone × X
Source : Set → Set
Source X = SourceId × X
SourceWords : Set → Set
SourceWords = Source ∘ Fwd ∘ Milestoned

forgetMilestone : {X : Set} → SourceWords X → Source (Fwd X)
forgetMilestone sw = (Over.travSnd ∘ Over.travFwd) _×_.snd sw

suffixEndSentence : String → EndSentence
suffixEndSentence x = go not-end-sentence $ primStringToList x
  where
  go : EndSentence → Fwd Char → EndSentence
  go s [] = s
  go s ('.' :> xs) = end-sentence
  go s (';' :> xs) = end-sentence
  go s (_ :> xs) = go s xs

prepareContents : Fwd PS.Content → Fwd (Milestoned (String × EndSentence))
prepareContents = go emptyMilestone
  where
  open Traverse
  go : Milestone → Fwd PS.Content → Fwd (Milestoned (String × EndSentence))
  go m [] = []
  go m (PS.milestone (PS.verse x) :> xs) = go (Over.travFst (const (some x)) m) xs 
  go m (PS.milestone PS.paragraph :> xs) = go (Over.travSnd next¶ m) xs 
  go m (PS.word (PS.word p t s) :> xs) = m , t , suffixEndSentence s :> go m xs

prepareSource : String → PS.Source → SourceWords $ String × EndSentence
prepareSource groupId s = sourceId groupId (PS.Source.getId s) , prepareContents (PS.Source.getContents s)

prepareGroup : PS.Group → Fwd ∘ SourceWords $ String × EndSentence
prepareGroup g = Fwd.map (prepareSource (PS.Group.getId g)) (PS.Group.getSources g)
