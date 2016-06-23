module Core where

open import Agda.Primitive
open import Agda.Builtin.Equality

module Inhabit where
  data ⊥ : Set where

  open import Agda.Builtin.Bool
  open import Agda.Builtin.Unit
  [_] : Bool → Set
  [ false ] = ⊥
  [ true ] = ⊤

  from-⊥ : {la : Level} → {A : Set la} → ⊥ → A
  from-⊥ ()

module Equivalence where
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

  open Equivalence
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

module Sum where
  infixr 4 _+_
  infix 1 _<| |>_
  data _+_ {la lb : Level} (A : Set la) (B : Set lb) : Set (la ⊔ lb) where
    _<| : (a : A) → A + B
    |>_ : (b : B) → A + B

  module Choice where
    open import Agda.Builtin.Bool
    is<|_ is|>_ : {la lb : Level} {A : Set la} {B : Set lb} → (A + B) → Bool
    is<| (a <|) = true
    is<| (|> b) = false
    is|> (a <|) = false
    is|> (|> b) = true

  open Equivalence
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

module Vector where
  open import Agda.Builtin.Nat
  data Vec {la : Level} (A : Set la) : Nat → Set la where
    [] : Vec A 0
    _∷_ : A → {n : Nat} → Vec A n → Vec A (suc n)

  record Vector {la : Level} (A : Set la) : Set la where
    constructor vector
    field
      {count} : Nat
      items : Vec A count

  open import Agda.Builtin.List

  open Equivalence
  list≅vector : {la lb : Level} {A : Set la} {B : Set lb} → List A ≅ Vector A
  list≅vector {A = A} {B = B} = equivalence there back left right
    where
    there : List A → Vector A
    there [] = vector []
    there (x ∷ xs) = vector (x ∷ Vector.items (there xs))

    back : Vector A → List A
    back (vector []) = []
    back (vector (x ∷ items)) = x ∷ back (vector items)

    left : (xs : List A) → back (there xs) ≡ xs
    left [] = refl
    left (x ∷ xs) rewrite left xs = refl

    right : (xs : Vector A) → there (back xs) ≡ xs
    right (vector []) = refl
    right (vector (x ∷ items)) rewrite right (vector items) = refl
