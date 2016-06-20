module Equivalence.Extensional where

open import Agda.Primitive
open import Agda.Builtin.Equality

infix 4 _≅_
record _≅_ {la lb : Level} (A : Set la) (B : Set lb) : Set (la ⊔ lb) where
  constructor equivalence
  field
    there : A → B
    back : B → A
    left : (a : A) → back (there a) ≡ a
    right : (b : B) → there (back b) ≡ b

reflexivity
  : {la : Level}
  → {A : Set la}
  → A ≅ A
reflexivity = equivalence (λ a → a) (λ a → a) (λ _ → refl) (λ _ → refl)

symmetry
  : {la lb : Level}
  → {A : Set la} {B : Set lb}
  → A ≅ B
  → B ≅ A
symmetry (equivalence there back left right) = equivalence back there right left

transitivity
  : {la lb lc : Level}
  → {A : Set la} {B : Set lb} {C : Set lc}
  → A ≅ B
  → B ≅ C
  → A ≅ C
transitivity
  {A = A} {B = B} {C = C}
  (equivalence there1 back1 left1 right1)
  (equivalence there2 back2 left2 right2)
  = equivalence there back left right
  where
    there : A → C
    there a = there2 (there1 a)

    back : C → A
    back c = back1 (back2 c)

    left : (a : A) → back (there a) ≡ a
    left a rewrite left2 (there1 a) | left1 a = refl

    right : (c : C) → there (back c) ≡ c
    right c rewrite right1 (back2 c) | right2 c = refl

