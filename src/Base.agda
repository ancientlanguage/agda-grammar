module Base where

infixr 4 _+_
infixr 5 _×_
infixr 1 _,_
infix 1 _~_

record ⊤ : Set where
  constructor tt

data _+_ (A B : Set) : Set where
  inl : (a : A) → A + B
  inr : (b : B) → A + B

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst

open import Agda.Builtin.List

module ListM where
  concat : {A : Set} → List (List A) → List A
  concat [] = []
  concat ([] ∷ xss) = concat xss
  concat ((x ∷ xs) ∷ xss) = x ∷ concat (xs ∷ xss)

  infixr 1 _++_
  _++_ : {A : Set} → (xs ys : List A) → List A
  [] ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

  concatMap : {A B : Set} (f : A → List B) → List A → List B
  concatMap f [] = []
  concatMap f (x ∷ xs) = f x ++ concatMap f xs

  map : {A B : Set} (f : A → B) (xs : List A) → List B
  map f [] = []
  map f (x ∷ xs) = f x ∷ map f xs

open import Agda.Builtin.Nat
  using (Nat)
  using (zero)
  using (suc)
open import Agda.Builtin.Equality

module Eq where
  record Inspect {A : Set} {B : A → Set} (f : (x : A) → B x) (x : A) (y : B x) : Set where
    constructor inspected
    field eq : f x ≡ y

  inspect : {A : Set} {B : A -> Set} (f : (x : A) -> B x) (x : A)
    -> Inspect f x (f x)
  inspect f x = inspected refl

  sym : {A : Set} -> {x y : A} -> x ≡ y -> y ≡ x
  sym refl = refl

  cong : {A B : Set} -> (f : A -> B) -> {x y : A} -> x ≡ y -> f x ≡ f y
  cong _ refl = refl

  trans : {A : Set} -> {x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
  trans refl refl = refl

  subst : {A : Set} {x y : A} (p : x ≡ y) {P : A → Set} (Px : P x) → P y
  subst refl Px = Px


record _~_ (A B : Set) : Set where
  field
    to : A → B
    from : B → A
    to-from : (b : B) → to (from b) ≡ b
    from-to : (a : A) → from (to a) ≡ a

module +Comm (A B : Set) where
  to : (A + B) → (B + A)
  to (inl a) = (inr a)
  to (inr b) = (inl b)
  
  from : (B + A) → (A + B)
  from (inl b) = (inr b)
  from (inr a) = (inl a)

  to-from : (ba : B + A) → to (from ba) ≡ ba
  to-from (inl b) = refl
  to-from (inr a) = refl

  from-to : (ab : A + B) → from (to ab) ≡ ab
  from-to (inl a) = refl
  from-to (inr b) = refl

+comm : {A B : Set} → (A + B) ~ (B + A)
+comm {A} {B} = record { +Comm A B }

data _×N_ (A : Set) : Nat → Set where
  none : A ×N zero
  add : (a : A) {n : Nat} (rest : A ×N n) → A ×N (suc n)

data List_≥_ (A : Set) (n : Nat) : Set where
  list≥ : (initial : A ×N n) (rest : List A) → List A ≥ n

data List1 (A : Set) : Set where
  list1 : (a : A) (rest : List A) → List1 A

module List1M where
  prepend : {A : Set} (a : A) (list : List1 A) → List1 A
  prepend a (list1 a2 rest) = list1 a (a2 ∷ rest)

module ×List (A : Set) where
  to : List A → ⊤ + A × List A
  to [] = inl _
  to (x ∷ xs) = inr (x , xs)

  from : ⊤ + A × List A → List A
  from (inl tt) = []
  from (inr (x , xs)) = x ∷ xs

  to-from : (x : ⊤ + A × List A) → to (from x) ≡ x
  to-from (inl tt) = refl
  to-from (inr (x , xs)) = refl

  from-to : (xs : List A) → from (to xs) ≡ xs
  from-to [] = refl
  from-to (x ∷ xs) = refl

×List : {A : Set} → List A ~ ⊤ + A × List A
×List {A} = record { ×List A }

module +GroupAdjacent (A B : Set) where
  to : List (A + B) → List B × List (List1 A × List1 B) × List A
  to [] = [] , [] , []
  to (inl a ∷ xs) with to xs
  to (inl a ∷ xs) | [] , [] , as                        = [] , [] , a ∷ as
  to (inl a ∷ xs) | [] , (list1 a2 as , bs) ∷ abs , asr = [] , (list1 a (a2 ∷ as) , bs) ∷ abs , asr
  to (inl a ∷ xs) | b ∷ bs , abs , as                   = [] , (list1 a [] , list1 b bs) ∷ abs , as
  to (inr b ∷ xs) with to xs
  … | bs , abs , as = b ∷ bs , abs , as

  from : List B × List (List1 A × List1 B) × List A → List (A + B)
  from (bs , abs , as) = map inr bs ++ concatMap middle abs ++ map inl as
    where
    open ListM
    middle : List1 A × List1 B → List (A + B)
    middle (list1 a as , list1 b bs) = inl a ∷ map inl as ++ inr b ∷ map inr bs

  to-injective : (x y : List (A + B)) (eq : to x ≡ to y) → x ≡ y
  to-injective [] [] eq = refl
  to-injective [] (inl a ∷ ys) eq with to ys
  to-injective [] (inl a ∷ ys) () | [] , [] , as
  to-injective [] (inl a ∷ ys) () | [] , (list1 a₁ rest , snd) ∷ abs , as
  to-injective [] (inl a ∷ ys) () | x ∷ bs , abs , as
  to-injective [] (inr b ∷ ys) ()
  to-injective (inl a ∷ xs) [] eq with to xs
  to-injective (inl a ∷ xs) [] () | [] , [] , as
  to-injective (inl a ∷ xs) [] () | [] , (list1 a₁ rest , snd) ∷ abs , as
  to-injective (inl a ∷ xs) [] () | x ∷ bs , abs , as
  to-injective (inr b ∷ xs) [] ()
  to-injective (inl ax ∷ xs) (inl ay ∷ ys) eq with to xs | Eq.inspect to xs | to ys | Eq.inspect to ys
  to-injective (inl ax ∷ xs) (inl .ax ∷ ys) refl | [] , [] , asx | Eq.inspected eqxs | [] , [] , .asx | Eq.inspected eqys =
    Eq.cong (inl ax ∷_)
      (to-injective xs ys (Eq.trans eqxs (Eq.sym eqys)))
  to-injective (inl ax ∷ xs) (inl ay ∷ ys) () | [] , [] , asx | Eq.inspected eqxs | [] , (list1 a rest , snd) ∷ absy , asy | Eq.inspected eqys
  to-injective (inl ax ∷ xs) (inl ay ∷ ys) () | [] , (list1 a rest , snd) ∷ absx , asx | Eq.inspected eqxs | [] , [] , asy | Eq.inspected eqys
  to-injective (inl ax ∷ xs) (inl .ax ∷ ys) refl | [] , (list1 a rest , snd) ∷ absx , asx | Eq.inspected eqxs | [] , (list1 .a .rest , .snd) ∷ .absx , .asx | Eq.inspected eqys =
    Eq.cong (inl ax ∷_)
      (to-injective xs ys (Eq.trans eqxs (Eq.sym eqys)))
  to-injective (inl ax ∷ xs) (inl ay ∷ ys) () | [] , [] , asx | Eq.inspected eqxs | x ∷ bsy , [] , asy | Eq.inspected eqys
  to-injective (inl ax ∷ xs) (inl ay ∷ ys) () | [] , (list1 a rest , snd) ∷ absx , asx | Eq.inspected eqxs | x ∷ bsy , [] , asy | Eq.inspected eqys
  to-injective (inl ax ∷ xs) (inl ay ∷ ys) () | [] , [] , asx | Eq.inspected eqxs | x ∷ bsy , x₁ ∷ absy , asy | Eq.inspected eqys
  to-injective (inl ax ∷ xs) (inl ay ∷ ys) () | [] , (list1 a rest , snd) ∷ absx , asx | Eq.inspected eqxs | x ∷ bsy , x₁ ∷ absy , asy | Eq.inspected eqys
  to-injective (inl ax ∷ xs) (inl ay ∷ ys) () | x ∷ bsx , absx , asx | Eq.inspected eqxs | [] , [] , asy | Eq.inspected eqys
  to-injective (inl ax ∷ xs) (inl ay ∷ ys) () | x ∷ bsx , absx , asx | Eq.inspected eqxs | [] , (list1 a rest , snd) ∷ absy , asy | Eq.inspected eqys
  to-injective (inl ax ∷ xs) (inl .ax ∷ ys) refl | bx ∷ bsx , absx , asx | Eq.inspected eqxs | .bx ∷ .bsx , .absx , .asx | Eq.inspected eqys =
    Eq.cong (inl ax ∷_)
      (to-injective xs ys (Eq.trans eqxs (Eq.sym eqys)))
  to-injective (inl a ∷ xs) (inr b ∷ ys) eq with to xs | Eq.inspect to xs | to ys | Eq.inspect to ys
  to-injective (inl a ∷ xs) (inr b ∷ ys) () | [] , [] , asx | Eq.inspected eqxs | bsy , absy , asy | Eq.inspected eqys
  to-injective (inl a ∷ xs) (inr b ∷ ys) () | [] , (list1 a₁ rest , snd) ∷ absx , asx | Eq.inspected eqxs | bsy , absy , asy | Eq.inspected eqys
  to-injective (inl a ∷ xs) (inr b ∷ ys) () | x ∷ bsx , absx , asx | Eq.inspected eqxs | bsy , absy , asy | Eq.inspected eqys
  to-injective (inr b ∷ xs) (inl a ∷ ys) eq with to xs | Eq.inspect to xs | to ys | Eq.inspect to ys
  to-injective (inr b ∷ xs) (inl a ∷ ys) () | bsx , absx , asx | Eq.inspected eqxs | [] , [] , asy | Eq.inspected eqys
  to-injective (inr b ∷ xs) (inl a ∷ ys) () | bsx , absx , asx | Eq.inspected eqxs | [] , (list1 a₁ rest , snd) ∷ absy , asy | Eq.inspected eqys
  to-injective (inr b ∷ xs) (inl a ∷ ys) () | bsx , absx , asx | Eq.inspected eqxs | x ∷ bsy , absy , asy | Eq.inspected eqys
  to-injective (inr bx ∷ xs) (inr by ∷ ys) eq with to xs | Eq.inspect to xs | to ys | Eq.inspect to ys
  to-injective (inr bx ∷ xs) (inr .bx ∷ ys) refl | bsx , absx , asx | Eq.inspected eqxs | .bsx , .absx , .asx | Eq.inspected eqys =
    Eq.cong (inr bx ∷_)
      (to-injective xs ys (Eq.trans eqxs (Eq.sym eqys)))

  to-surjective : (y : List B × List (List1 A × List1 B) × List A) → Σ (List (A + B)) (λ x → to x ≡ y)
  to-surjective (bs , abs , as) = {!!}
