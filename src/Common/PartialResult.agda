module Common.PartialResult where

open import Agda.Primitive
open import Agda.Builtin.Unit
open import Prelude.Empty
open import Common.Sum

infixl 1 _⁇_

data _⁇_
  {la le : Level}
  (A : Set la)
  (E : Set le)
  : Set (la ⊔ le)
  where
  defined : A → A ⁇ E
  undefined : E → A ⁇ E

Defined?
  : {la le : Level}
  → {A : Set la}
  → {E : Set le}
  → A ⁇ E
  → Set
Defined? (defined x) = ⊤
Defined? (undefined x) = ⊥

extractDefined
  : {la le : Level}
  → {A : Set la}
  → {E : Set le}
  → (x : A ⁇ E)
  → {_ : Defined? x}
  → A
extractDefined (defined x) = x
extractDefined (undefined x) {}

joinDefinedAux
  : {lb lc le : Level}
  → {B : Set lb}
  → {C : Set lc}
  → {E : Set le}
  → (B → C ⁇ E)
  → (B ⁇ E)
  → (C ⁇ E)
joinDefinedAux g (defined x) = g x
joinDefinedAux g (undefined x) = undefined x

joinDefined
  : {la lb lc le : Level}
  → {A : Set la}
  → {B : Set lb}
  → {C : Set lc}
  → {E : Set le}
  → (A → B ⁇ E)
  → (B → C ⁇ E)
  → (A → C ⁇ E)
joinDefined f g x = joinDefinedAux g (f x)
