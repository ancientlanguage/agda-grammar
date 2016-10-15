module AncientLanguage.Grammar.Greek.Script.Case-Capital where

open import AncientLanguage.Abstraction
open import AncientLanguage.Grammar.Greek.Script.Letter
open import AncientLanguage.Grammar.Greek.Script.Capital

data Error : Set where
  empty-word : Error
  non-initial-upper : Letter → Error

validate-lower : {A : Set} → Fwd (Letter × Case × A) → Fwd Error + Fwd (Letter × A)
validate-lower [] = Sum.inr []
validate-lower (x :> xs) with validate-lower xs
validate-lower (l , upper , a :> xs) | Sum.inl es = Sum.inl (non-initial-upper l :> es)
validate-lower (l , lower , a :> xs) | Sum.inl es = Sum.inl es
validate-lower (l , upper , a :> xs) | Sum.inr xs' = Sum.inl (non-initial-upper l :> [])
validate-lower (l , lower , a :> xs) | Sum.inr xs' = Sum.inr (l , a :> xs')

to : {A : Set} → Fwd (Letter × Case × A) → Fwd Error + (Fwd (Letter × A) × Capital)
to [] = Sum.inl (empty-word :> []) 
to (x :> xs) with validate-lower xs
to (x :> xs) | Sum.inl es = Sum.inl es
to (l , c , a :> xs) | Sum.inr xs' = Sum.inr ((l , a :> xs') , first-case c)
  where
  first-case : Case → Capital
  first-case upper = capital
  first-case lower = lowercase

map-to
  : {A B : Set}
  → (A → Letter × Case × B)
  → Fwd A
  → Fwd Error + (Fwd (Letter × B) × Capital)
map-to f xs = to $ Fwd.map f xs

set-case : {A : Set} → Case → Letter × A → Letter × Case × A
set-case c (l , a) = l , c , a

from : {A : Set} → Fwd (Letter × A) × Capital → Fwd (Letter × Case × A)
from ([] , capital) = []
from ((x :> xs) , capital) = set-case upper x :> Fwd.map (set-case lower) xs
from (xs , lowercase) = Fwd.map (set-case lower) xs

module Test where
  open import AncientLanguage.Grammar.Greek.Script.Symbol
  open import AncientLanguage.Grammar.Greek.Script.Mark
  import AncientLanguage.Grammar.Greek.Script.Unicode-Symbol as Unicode-Symbol
  import AncientLanguage.Grammar.Greek.Script.Symbol-Letter as Symbol-Letter
  cap-word : Fwd (Letter × Case × Final + Mark)
  cap-word =
    (TraverseId.fwd ∘ TraverseId.inl)
    (toProduct ∘ Symbol-Letter.to)
    (Sum.asInr (Unicode-Symbol.stringToSymbol "Βίβλος"))
