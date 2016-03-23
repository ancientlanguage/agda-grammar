module Common.PartialResult where

open import Agda.Primitive
open import Agda.Builtin.Unit
open import Prelude.Monoidal.Void
open import Prelude.Monoidal.Product.Indexed
open import Common.Sum

open Π

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
Defined? (undefined x) = 𝟘

extractDefined
  : {la le : Level}
  → {A : Set la}
  → {E : Set le}
  → (x : A ⁇ E)
  → {_ : Defined? x}
  → A
extractDefined (defined x) = x
extractDefined (undefined x) {}

mapUndefined
  : {la le1 le2 : Level}
  → {A : Set la}
  → {E1 : Set le1}
  → {E2 : Set le2}
  → (E1 → E2)
  → A ⁇ E1
  → A ⁇ E2
mapUndefined f (defined x) = defined x
mapUndefined f (undefined x) = undefined (f x)

liftDomain
  : {lb lc le : Level}
  → {B : Set lb}
  → {C : Set lc}
  → {E : Set le}
  → (B → C ⁇ E)
  → (B ⁇ E)
  → (C ⁇ E)
liftDomain g (defined x) = g x
liftDomain g (undefined x) = undefined x

joinDefined
  : {la lb lc le : Level}
  → {A : Set la}
  → {B : Set lb}
  → {C : Set lc}
  → {E : Set le}
  → (A → B ⁇ E)
  → (B → C ⁇ E)
  → (A → C ⁇ E)
joinDefined f g = liftDomain g ∘ f
