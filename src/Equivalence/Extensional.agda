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

module Properties where
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

module Product where
  infixl 5 _×_
  infixr 3 _,_
  data _×_ {la lb : Level} (A : Set la) (B : Set lb) : Set (la ⊔ lb) where
    _,_ : A → B → A × B

  over
    : {la lb lc ld : Level}
    → {A : Set la} {B : Set lb} {C : Set lc} {D : Set ld}
    → A ≅ C
    → B ≅ D
    → (A × B) ≅ (C × D)
  over
    {A = A} {B = B} {C = C} {D = D}
    (equivalence thereAC backAC leftAC rightAC)
    (equivalence thereBD backBD leftBD rightBD)
    = equivalence there back left right
     where
       give
         : {la lb lc ld : Level}
         → {A : Set la} {B : Set lb} {C : Set lc} {D : Set ld}
         → (A → C)
         → (B → D)
         → (A × B) → (C × D)
       give f g (a , b) = f a , g b

       there : A × B → C × D
       there = give thereAC thereBD

       back : C × D → A × B
       back = give backAC backBD

       left : (x : A × B) → back (there x) ≡ x
       left (a , b) rewrite leftAC a | leftBD b = refl

       right : (x : C × D) → there (back x) ≡ x
       right (c , d) rewrite rightAC c | rightBD d = refl
