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

module Function where
  id : {la : Level} → {A : Set la} → A → A
  id x = x

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
    reflexivity = equivalence Function.id Function.id (λ _ → refl) (λ _ → refl)

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

  over-fst
    : {la lb lc : Level}
    → {A : Set la} {B : Set lb} {C : Set lc}
    → A ≅ C
    → (A × B) ≅ (C × B)
  over-fst p = over p Equivalence.Properties.reflexivity

  over-snd
    : {la lb ld : Level}
    → {A : Set la} {B : Set lb} {D : Set ld}
    → B ≅ D
    → (A × B) ≅ (A × D)
  over-snd p = over Equivalence.Properties.reflexivity p

module Sum where
  infixr 4 _⊕_
  data _⊕_ {la lb : Level} (A : Set la) (B : Set lb) : Set (la ⊔ lb) where
    inj1 : (a : A) → A ⊕ B
    inj2 : (b : B) → A ⊕ B

  module Which where
    open import Agda.Builtin.Bool
    inj1? inj2? : {la lb : Level} {A : Set la} {B : Set lb} → (A ⊕ B) → Bool
    inj1? (inj1 a) = true
    inj1? (inj2 b) = false
    inj2? (inj1 a) = false
    inj2? (inj2 b) = true

  open Equivalence
  over
    : {la lb lc ld : Level}
    → {A : Set la} {B : Set lb} {C : Set lc} {D : Set ld}
    → A ≅ C
    → B ≅ D
    → (A ⊕ B) ≅ (C ⊕ D)
  over
    {A = A} {B = B} {C = C} {D = D}
    (equivalence thereAC backAC leftAC rightAC)
    (equivalence thereBD backBD leftBD rightBD)
    = equivalence there back left right
    where
      there : A ⊕ B → C ⊕ D
      there (inj1 a) = inj1 (thereAC a)
      there (inj2 b) = inj2 (thereBD b)

      back : C ⊕ D → A ⊕ B
      back (inj1 a) = inj1 (backAC a)
      back (inj2 b) = inj2 (backBD b)

      left : (x : A ⊕ B) → back (there x) ≡ x
      left (inj1 a) rewrite leftAC a = refl
      left (inj2 b) rewrite leftBD b = refl

      right : (x : C ⊕ D) → there (back x) ≡ x
      right (inj1 a) rewrite rightAC a = refl
      right (inj2 b) rewrite rightBD b = refl

  over-inj1
    : {la lb lc : Level}
    → {A : Set la} {B : Set lb} {C : Set lc}
    → A ≅ C
    → (A ⊕ B) ≅ (C ⊕ B)
  over-inj1 p = over p Equivalence.Properties.reflexivity

  over-inj2
    : {la lb ld : Level}
    → {A : Set la} {B : Set lb} {D : Set ld}
    → B ≅ D
    → (A ⊕ B) ≅ (A ⊕ D)
  over-inj2 p = over Equivalence.Properties.reflexivity p

  module Assert where
    open import Agda.Builtin.List
    assert-inj2 : {la lb : Level} {A : Set la} {B : Set lb} → List (A ⊕ B) → List A ⊕ List B
    assert-inj2 [] = inj2 []
    assert-inj2 (x ∷ xs) with assert-inj2 xs
    assert-inj2 (inj1 a ∷ xs) | inj1 as = inj1 (a ∷ as)
    assert-inj2 (inj2 b ∷ xs) | inj1 as = inj1 as
    assert-inj2 (inj1 a ∷ xs) | inj2 bs = inj1 (a ∷ [])
    assert-inj2 (inj2 b ∷ xs) | inj2 bs = inj2 (b ∷ bs)

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
