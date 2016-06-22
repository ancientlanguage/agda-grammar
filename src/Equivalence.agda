module Equivalence where

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
  infixr 5 _×_
  infixr 3 _,_
  record _×_ {la lb : Level} (A : Set la) (B : Set lb) : Set (la ⊔ lb) where
    constructor _,_
    field
      fst : A
      snd : B

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
      open _×_

      there : A × B → C × D
      there (a , b) = thereAC a , thereBD b

      back : C × D → A × B
      back (c , d) = backAC c , backBD d

      left : (x : A × B) → back (there x) ≡ x
      left (a , b) rewrite leftAC a | leftBD b = refl

      right : (x : C × D) → there (back x) ≡ x
      right (c , d) rewrite rightAC c | rightBD d = refl

module Coproduct where
  infixr 4 _+_
  data _+_ {la lb : Level} (A : Set la) (B : Set lb) : Set (la ⊔ lb) where
    _<| : (a : A) → A + B
    |>_ : (b : B) → A + B

  over
    : {la lb lc ld : Level}
    → {A : Set la} {B : Set lb} {C : Set lc} {D : Set ld}
    → A ≅ C
    → B ≅ D
    → (A + B) ≅ (C + D)
  over
    {A = A} {B = B} {C = C} {D = D}
    (equivalence thereAC backAC leftAC rightAC)
    (equivalence thereBD backBD leftBD rightBD)
    = equivalence there back left right
    where
      there : A + B → C + D
      there (a <|) = thereAC a <|
      there (|> b) = |> thereBD b

      back : C + D → A + B
      back (a <|) = backAC a <|
      back (|> b) = |> backBD b

      left : (x : A + B) → back (there x) ≡ x
      left (a <|) rewrite leftAC a = refl
      left (|> b) rewrite leftBD b = refl

      right : (x : C + D) → there (back x) ≡ x
      right (a <|) rewrite rightAC a = refl
      right (|> b) rewrite rightBD b = refl
