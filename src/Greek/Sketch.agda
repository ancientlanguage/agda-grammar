{-# OPTIONS --exact-split #-}

module Greek.Sketch where

open import Agda.Builtin.Char
open import Agda.Builtin.Equality
open import Agda.Builtin.String
open import Agda.Builtin.List
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.FromString
open import Agda.Builtin.Unit

infixl 7 _×_
infixl 6 _+_
infixr 4 _++_
infixr 3 _,_
infix 1 _≅_

data ⊥ : Set where
⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

data _+_ (A B : Set) : Set where
  inl : A → A + B
  inr : B → A + B

assume-inr : {A B : Set} → A + B → Set
assume-inr (inl a) = ⊥
assume-inr (inr b) = ⊤

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

data Pair (A : Set) (B : A → Set) : Set where
  pair : (a : A) → (b : B a) → Pair A B

List∅ : Set
List∅ = ⊤

List+ : Set → Set
List+ A = A × List A

module ListM where
  map : {A B : Set} → (A → B) → List A → List B
  map f [] = []
  map f (x ∷ xs) = f x ∷ map f xs

_++_ : {A : Set} → (xs ys : List A) → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

record _≅_ (A B : Set) : Set where
  constructor equiv
  field
    to : A → B
    from : B → A
    to-from : (x : B) → to (from x) ≡ x
    from-to : (x : A) → from (to x) ≡ x

module Eq where
  id : {A : Set} → A ≅ A
  id = equiv (λ x → x) (λ x → x) (λ _ → refl) (λ _ → refl)

  infixr 9 _∘_
  _∘_ : {A B C : Set} → B ≅ C → A ≅ B → A ≅ C
  _∘_ {A} {B} {C} (equiv toY fromY to-fromY from-toY) (equiv toX fromX to-fromX from-toX) = equiv to from to-from from-to
    where
    to : A → C
    to x = toY (toX x)

    from : C → A
    from x = fromX (fromY x)

    to-from : (x : C) → to (from x) ≡ x
    to-from x rewrite to-fromX (fromY x) | to-fromY x = refl

    from-to : (x : A) → from (to x) ≡ x
    from-to x rewrite from-toY (toX x) | from-toX x = refl

move-inr : {A B C : Set}
  → (eq : A ≅ B + C)
  → (a : A)
  → {p : assume-inr (_≅_.to eq a)}
  → C
move-inr eq a {p} with _≅_.to eq a
move-inr eq a {p} | inl c = ⊥-elim p
move-inr eq a | inr c = c

infixl 1 _|>>_
_|>>_ : {A B C : Set}
  → (a : A)
  → (eq : A ≅ B + C)
  → {p : assume-inr (_≅_.to eq a)}
  → C
_|>>_ a eq {p} = move-inr eq a {p}

emptiness : {A : Set} → List A ≅ List∅ + List+ A
emptiness {A} = equiv to from to-from from-to
  where
  to : List A → List∅ + List+ A
  to [] = inl _
  to (x ∷ xs) = inr (x , xs)
  from : List∅ + List+ A → List A
  from (inl tt) = []
  from (inr (x , xs)) = x ∷ xs
  to-from : (x : List∅ + List+ A) → to (from x) ≡ x
  to-from (inl tt) = refl
  to-from (inr (_ , _)) = refl
  from-to : (x : List A) → from (to x) ≡ x
  from-to [] = refl
  from-to (_ ∷ _) = refl

over-list : {A B : Set} → A ≅ B → List A ≅ List B
over-list {A} {B} (equiv toX fromX to-fromX from-toX) = equiv to from to-from from-to
  where
  to : List A → List B
  to [] = []
  to (x ∷ xs) = toX x ∷ to xs

  from : List B → List A
  from [] = []
  from (x ∷ xs) = fromX x ∷ from xs

  to-from : (xs : List B) → to (from xs) ≡ xs
  to-from [] = refl
  to-from (x ∷ xs) rewrite to-fromX x | to-from xs = refl

  from-to : (xs : List A) → from (to xs) ≡ xs
  from-to [] = refl
  from-to (x ∷ xs) rewrite from-toX x | from-to xs = refl

swap-sum : {A B : Set} → A + B ≅ B + A
swap-sum = equiv swap swap same same
  where
  swap : {A B : Set} → A + B → B + A
  swap (inl x) = inr x
  swap (inr x) = inl x

  same : {A B : Set} → (x : A + B) → swap (swap x) ≡ x
  same (inl x) = refl
  same (inr x) = refl

swap-product : {A B : Set} → A × B ≅ B × A
swap-product = equiv swap swap same same
  where
  swap : {A B : Set} → A × B → B × A
  swap (fst , snd) = snd , fst

  same : {A B : Set} → (x : A × B) → swap (swap x) ≡ x
  same (fst , snd) = refl

product-top : {A : Set} → A × ⊤ ≅ A
product-top {A} = equiv to from to-from from-to
  where
  to : A × ⊤ → A
  to (fst , snd) = fst
  from : A → A × ⊤
  from x = x , _
  to-from : (x : A) → to (from x) ≡ x
  to-from x = refl
  from-to : (x : A × ⊤) → from (to x) ≡ x
  from-to (fst , tt) = refl

over-product : {A B C D : Set} → A ≅ B → C ≅ D → A × C ≅ B × D
over-product {A} {B} {C} {D} (equiv toX fromX to-fromX from-toX) (equiv toY fromY to-fromY from-toY) = equiv to from to-from from-to
  where
  to : A × C → B × D
  to (a , c) = (toX a , toY c)

  from : B × D → A × C
  from (b , c) = (fromX b , fromY c)

  to-from : (x : B × D) → to (from x) ≡ x
  to-from (b , d) rewrite to-fromX b | to-fromY d = refl

  from-to : (x : A × C) → from (to x) ≡ x
  from-to (a , c) rewrite from-toX a | from-toY c = refl

over-fst : {A B C : Set} → A ≅ B → A × C ≅ B × C
over-fst eq = over-product eq Eq.id

over-snd : {A B C : Set} → A ≅ B → C × A ≅ C × B
over-snd eq = over-product Eq.id eq

over-list+ : {A B : Set} → A ≅ B → List+ A ≅ List+ B
over-list+ eq = over-product eq (over-list eq)

promote-list+ : {A B : Set} → List A ≅ B → List+ A ≅ A × B
promote-list+ {A} {B} eq = over-snd eq

over-sum : {A B C D : Set} → A ≅ B → C ≅ D → A + C ≅ B + D
over-sum {A} {B} {C} {D} (equiv toX fromX to-fromX from-toX) (equiv toY fromY to-fromY from-toY) = equiv to from to-from from-to
  where
  to : A + C → B + D
  to (inl a) = inl (toX a)
  to (inr c) = inr (toY c)

  from : B + D → A + C
  from (inl b) = inl (fromX b)
  from (inr d) = inr (fromY d)

  to-from : (x : B + D) → to (from x) ≡ x
  to-from (inl b) rewrite to-fromX b = refl
  to-from (inr d) rewrite to-fromY d = refl

  from-to : (x : A + C) → from (to x) ≡ x
  from-to (inl a) rewrite from-toX a = refl
  from-to (inr c) rewrite from-toY c = refl

over-inl : {A B C : Set} → A ≅ B → A + C ≅ B + C
over-inl eq = over-sum eq Eq.id

over-inr : {A B C : Set} → A ≅ B → C + A ≅ C + B
over-inr eq = over-sum Eq.id eq

infix 3 _∈_
data _∈_ {A : Set} : A → List A → Set where
  top : (x : A) → (xs : List A) → x ∈ x ∷ xs
  pop : (x y : A) → (xs : List A) → x ∈ xs → x ∈ y ∷ xs

module Inspect where
  open import Agda.Primitive
  record Reveal_·_is_ {a b} {A : Set a} {B : A → Set b}
                      (f : (x : A) → B x) (x : A) (y : B x) :
                      Set (a ⊔ b) where
    constructor [_]
    field eq : f x ≡ y

  inspect : ∀ {a b} {A : Set a} {B : A → Set b}
            (f : (x : A) → B x) (x : A) → Reveal f · x is f x
  inspect f x = [ refl ]

group-inr
  : {A B : Set}
  → List (A + B)
  ≅ List B × List (A × List B)
group-inr {A} {B} = equiv to from to-from from-to
  where
  to-aux : A + B → List B × List (A × List B) → List B × List (A × List B)
  to-aux (inl a) (bs , xs) = [] , (a , bs) ∷ xs
  to-aux (inr b) (bs , xs) = b ∷ bs , xs

  to : List (A + B) → List B × List (A × List B)
  to [] = [] , []
  to (x ∷ xs) = to-aux x (to xs)

  from-prepend : List B → List (A + B) → List (A + B)
  from-prepend [] abs = abs
  from-prepend (b ∷ bs) abs = inr b ∷ from-prepend bs abs

  from-aux2 : List (A × List B) → List (A + B)
  from-aux2 [] = []
  from-aux2 ((a , bs) ∷ zs) = inl a ∷ from-prepend bs (from-aux2 zs)

  from : List B × List (A × List B) → List (A + B)
  from (bs , abs) = from-prepend bs (from-aux2 abs)

  to-from-aux : ∀ bs xs → to (from ([] , xs)) ≡ ([] , xs) → to (from (bs , xs)) ≡ (bs , xs)
  to-from-aux [] xs p = p
  to-from-aux (x ∷ bs) xs p rewrite to-from-aux bs xs p = refl

  to-from : (x : List B × List (A × List B)) → to (from x) ≡ x
  to-from ([] , []) = refl
  to-from ([] , (fst , []) ∷ xs) rewrite to-from ([] , xs) = refl
  to-from ([] , (fst , b ∷ bs) ∷ xs) rewrite to-from-aux bs xs (to-from ([] , xs)) = refl
  to-from (x ∷ fst , snd) rewrite to-from (fst , snd) = refl

  from-to : (x : List (A + B)) → from (to x) ≡ x
  from-to [] = refl
  from-to (inl a ∷ xs) rewrite from-to xs = refl
  from-to (inr b ∷ xs) rewrite from-to xs = refl

dist-product-fst-sum : {A B C : Set} → (A + B) × C ≅ A × C + B × C
dist-product-fst-sum {A} {B} {C} = equiv to from to-from from-to
  where
  to : (A + B) × C → A × C + B × C
  to (inl a , c) = inl (a , c)
  to (inr b , c) = inr (b , c)
  from : A × C + B × C → (A + B) × C
  from (inl (a , c)) = inl a , c
  from (inr (b , c)) = inr b , c
  to-from : (x : A × C + B × C) → to (from x) ≡ x
  to-from (inl (fst , snd)) = refl
  to-from (inr (fst , snd)) = refl
  from-to : (x : (A + B) × C) → from (to x) ≡ x
  from-to (inl x , snd) = refl
  from-to (inr x , snd) = refl

dist-product-snd-sum : {A B C : Set} → A × (B + C) ≅ A × B + A × C
dist-product-snd-sum {A} {B} {C} = p3 Eq.∘ p2
  where
  p1 : A × (B + C) ≅ (B + C) × A
  p1 = swap-product

  p2 : A × (B + C) ≅ B × A + C × A
  p2 = dist-product-fst-sum Eq.∘ p1

  p3 : B × A + C × A ≅ A × B + A × C
  p3 = over-sum swap-product swap-product

group-inr-snd
  : {A B : Set}
  → List (A + B)
  ≅ List B × List+ (A × List B) + List B
group-inr-snd {A} {B} = part4 ∘ part3 ∘ part2 ∘ part1 ∘ group-inr
  where
  open Eq using (_∘_)
  part1 : List B × List (A × List B)
    ≅ List B × (List∅ + List+ (A × List B))
  part1 = over-snd emptiness

  part2 : List B × (List∅ + List+ (A × List B))
    ≅ List B × List∅ + List B × List+ (A × List B)
  part2 = dist-product-snd-sum

  part3 : List B × List∅ + List B × List+ (A × List B)
    ≅ List B + List B × List+ (A × List B)
  part3 = over-inl product-top

  part4 : List B + List B × List+ (A × List B)
    ≅ List B × List+ (A × List B) + List B
  part4 = swap-sum

assoc-product-left : {A B C : Set} → A × (B × C) ≅ (A × B) × C
assoc-product-left {A} {B} {C} = equiv to from to-from from-to
  where
  to : A × (B × C) → (A × B) × C
  to (a , (b , c)) = (a , b) , c
  from : (A × B) × C → A × (B × C)
  from ((a , b) , c) = a , (b , c)
  to-from : (x : (A × B) × C) → to (from x) ≡ x
  to-from ((a , b) , c) = refl
  from-to : (x : A × (B × C)) → from (to x) ≡ x
  from-to (a , (b , c)) = refl

product-swap-right : {A B C : Set} → A × (B × C) ≅ B × (A × C)
product-swap-right {A} {B} {C} = equiv to from to-from from-to
  where
  to : A × (B × C) → B × (A × C)
  to (a , (b , c)) = b , (a , c)
  from : B × (A × C) → A × (B × C)
  from (b , (a , c)) = a , (b , c)
  to-from : (x : B × (A × C)) → to (from x) ≡ x
  to-from (b , (a , c)) = refl
  from-to : (x : A × (B × C)) → from (to x) ≡ x
  from-to (a , (b , c)) = refl

group-inr+
  : {A B : Set}
  → List+ (A + B)
  ≅ List+ B × List (A × List B)
  + List+ (A × List B)
group-inr+ {A} {B} = part5 ∘ part4 ∘ part3 ∘ part2
  where
  open Eq
  part1 : List (A + B) ≅ List B × List (A × List B)
  part1 = group-inr

  part2 : List+ (A + B) ≅ (A + B) × (List B × List (A × List B))
  part2 = promote-list+ part1

  part3 : (A + B) × (List B × List (A × List B))
    ≅ A × (List B × List (A × List B))
    + B × (List B × List (A × List B))
  part3 = dist-product-fst-sum

  part4
    : A × (List B × List (A × List B))
    + B × (List B × List (A × List B))
    ≅ (A × List B) × List (A × List B)
    + (B × List B) × List (A × List B)
  part4 = over-sum assoc-product-left assoc-product-left

  part5
    : (A × List B) × List (A × List B)
    + (B × List B) × List (A × List B)
    ≅ (B × List B) × List (A × List B)
    + (A × List B) × List (A × List B)
  part5 = swap-sum

data ConcreteLetter : Set where
  Α Β Γ Δ Ε Ζ Η Θ Ι Κ Λ Μ Ν Ξ Ο Π Ρ Σ Τ Υ Φ Χ Ψ Ω α β γ δ ε ζ η θ ι κ ƛ μ ν ξ ο π ρ σ ς τ υ φ χ ψ ω : ConcreteLetter
data Mark : Set where
  acute grave circumflex smooth rough diaeresis iota-sub : Mark

from-char : Char → Char + (ConcreteLetter + Mark)
from-char 'Α' = inr (inl Α)
from-char 'Β' = inr (inl Β)
from-char 'Γ' = inr (inl Γ)
from-char 'Δ' = inr (inl Δ)
from-char 'Ε' = inr (inl Ε)
from-char 'Ζ' = inr (inl Ζ)
from-char 'Η' = inr (inl Η)
from-char 'Θ' = inr (inl Θ)
from-char 'Ι' = inr (inl Ι)
from-char 'Κ' = inr (inl Κ)
from-char 'Λ' = inr (inl Λ)
from-char 'Μ' = inr (inl Μ)
from-char 'Ν' = inr (inl Ν)
from-char 'Ξ' = inr (inl Ξ)
from-char 'Ο' = inr (inl Ο)
from-char 'Π' = inr (inl Π)
from-char 'Ρ' = inr (inl Ρ)
from-char 'Σ' = inr (inl Σ)
from-char 'Τ' = inr (inl Τ)
from-char 'Υ' = inr (inl Υ)
from-char 'Φ' = inr (inl Φ)
from-char 'Χ' = inr (inl Χ)
from-char 'Ψ' = inr (inl Ψ)
from-char 'Ω' = inr (inl Ω)
from-char 'α' = inr (inl α)
from-char 'β' = inr (inl β)
from-char 'γ' = inr (inl γ)
from-char 'δ' = inr (inl δ)
from-char 'ε' = inr (inl ε)
from-char 'ζ' = inr (inl ζ)
from-char 'η' = inr (inl η)
from-char 'θ' = inr (inl θ)
from-char 'ι' = inr (inl ι)
from-char 'κ' = inr (inl κ)
from-char 'λ' = inr (inl ƛ)
from-char 'μ' = inr (inl μ)
from-char 'ν' = inr (inl ν)
from-char 'ξ' = inr (inl ξ)
from-char 'ο' = inr (inl ο)
from-char 'π' = inr (inl π)
from-char 'ρ' = inr (inl ρ)
from-char 'σ' = inr (inl σ)
from-char 'ς' = inr (inl ς)
from-char 'τ' = inr (inl τ)
from-char 'υ' = inr (inl υ)
from-char 'φ' = inr (inl φ)
from-char 'χ' = inr (inl χ)
from-char 'ψ' = inr (inl ψ)
from-char 'ω' = inr (inl ω)
from-char '\x0300' = inr (inr grave) -- COMBINING GRAVE ACCENT
from-char '\x0301' = inr (inr acute) -- COMBINING ACUTE ACCENT
from-char '\x0308' = inr (inr diaeresis) -- COMBINING DIAERESIS
from-char '\x0313' = inr (inr smooth) -- COMBINING COMMA ABOVE
from-char '\x0314' = inr (inr rough) -- COMBINING REVERSED COMMA ABOVE
from-char '\x0342' = inr (inr circumflex) -- COMBINING GREEK PERISPOMENI
from-char '\x0345' = inr (inr iota-sub) -- COMBINING GREEK YPOGEGRAMMENI
from-char x = inl x

from-any-string : String → List (Char + (ConcreteLetter + Mark))
from-any-string xs = ListM.map from-char (primStringToList (decompose xs))
  where
  open import Unicode.Decompose

string-expected
  : List (Char + (ConcreteLetter + Mark))
  ≅ List (ConcreteLetter + Mark) × List+ (Char × List (ConcreteLetter + Mark))
  + List (ConcreteLetter + Mark)
string-expected = group-inr-snd

from-string
  : (xs : String)
  → {{p : assume-inr (_≅_.to string-expected (from-any-string xs))}}
  → List (ConcreteLetter + Mark)
from-string xs {{p}} = move-inr string-expected (from-any-string xs) {p = p}

instance
  StringScript : IsString (List (ConcreteLetter + Mark))
  IsString.Constraint StringScript xs = assume-inr (_≅_.to string-expected (from-any-string xs))
  IsString.fromString StringScript xs = from-string xs

data Letter : Set where
  α β γ δ ε ζ η θ ι κ ƛ μ ν ξ ο π ρ σ τ υ φ χ ψ ω : Letter
data LetterCase : Set where
  upper lower : LetterCase
data Final : Set where
  n/a is-final not-final : Final

data NonSigma : Letter → Set where
  α : NonSigma α
  β : NonSigma β
  γ : NonSigma γ
  δ : NonSigma δ
  ε : NonSigma ε
  ζ : NonSigma ζ
  η : NonSigma η
  θ : NonSigma θ
  ι : NonSigma ι
  κ : NonSigma κ
  ƛ : NonSigma ƛ
  μ : NonSigma μ
  ν : NonSigma ν
  ξ : NonSigma ξ
  ο : NonSigma ο
  π : NonSigma π
  ρ : NonSigma ρ
  τ : NonSigma τ
  υ : NonSigma υ
  φ : NonSigma φ
  χ : NonSigma χ
  ψ : NonSigma ψ
  ω : NonSigma ω

data LetterCaseFinalD : Letter → LetterCase → Final → Set where
  non-sigma : {l : Letter} → NonSigma l → (c : LetterCase) → LetterCaseFinalD l c n/a
  sigma-upper-n/a : LetterCaseFinalD σ upper n/a
  sigma-lower-not-final : LetterCaseFinalD σ lower not-final
  sigma-lower-is-final : LetterCaseFinalD σ lower is-final

record LetterCaseFinal : Set where
  constructor letter-case-final
  field
    {letter} : Letter
    {case} : LetterCase
    {final} : Final
    combo : LetterCaseFinalD letter case final

concrete-abstract
  : ConcreteLetter
  ≅ LetterCaseFinal
concrete-abstract = equiv to from to-from from-to
  where
  to : ConcreteLetter → LetterCaseFinal
  to Α = letter-case-final (non-sigma α upper)
  to Β = letter-case-final (non-sigma β upper)
  to Γ = letter-case-final (non-sigma γ upper)
  to Δ = letter-case-final (non-sigma δ upper)
  to Ε = letter-case-final (non-sigma ε upper)
  to Ζ = letter-case-final (non-sigma ζ upper)
  to Η = letter-case-final (non-sigma η upper)
  to Θ = letter-case-final (non-sigma θ upper)
  to Ι = letter-case-final (non-sigma ι upper)
  to Κ = letter-case-final (non-sigma κ upper)
  to Λ = letter-case-final (non-sigma ƛ upper)
  to Μ = letter-case-final (non-sigma μ upper)
  to Ν = letter-case-final (non-sigma ν upper)
  to Ξ = letter-case-final (non-sigma ξ upper)
  to Ο = letter-case-final (non-sigma ο upper)
  to Π = letter-case-final (non-sigma π upper)
  to Ρ = letter-case-final (non-sigma ρ upper)
  to Σ = letter-case-final (sigma-upper-n/a)
  to Τ = letter-case-final (non-sigma τ upper)
  to Υ = letter-case-final (non-sigma υ upper)
  to Φ = letter-case-final (non-sigma φ upper)
  to Χ = letter-case-final (non-sigma χ upper)
  to Ψ = letter-case-final (non-sigma ψ upper)
  to Ω = letter-case-final (non-sigma ω upper)
  to α = letter-case-final (non-sigma α lower)
  to β = letter-case-final (non-sigma β lower)
  to γ = letter-case-final (non-sigma γ lower)
  to δ = letter-case-final (non-sigma δ lower)
  to ε = letter-case-final (non-sigma ε lower)
  to ζ = letter-case-final (non-sigma ζ lower)
  to η = letter-case-final (non-sigma η lower)
  to θ = letter-case-final (non-sigma θ lower)
  to ι = letter-case-final (non-sigma ι lower)
  to κ = letter-case-final (non-sigma κ lower)
  to ƛ = letter-case-final (non-sigma ƛ lower)
  to μ = letter-case-final (non-sigma μ lower)
  to ν = letter-case-final (non-sigma ν lower)
  to ξ = letter-case-final (non-sigma ξ lower)
  to ο = letter-case-final (non-sigma ο lower)
  to π = letter-case-final (non-sigma π lower)
  to ρ = letter-case-final (non-sigma ρ lower)
  to σ = letter-case-final (sigma-lower-not-final)
  to ς = letter-case-final (sigma-lower-is-final)
  to τ = letter-case-final (non-sigma τ lower)
  to υ = letter-case-final (non-sigma υ lower)
  to φ = letter-case-final (non-sigma φ lower)
  to χ = letter-case-final (non-sigma χ lower)
  to ψ = letter-case-final (non-sigma ψ lower)
  to ω = letter-case-final (non-sigma ω lower)

  from : LetterCaseFinal → ConcreteLetter
  from (letter-case-final (non-sigma α upper)) = Α
  from (letter-case-final (non-sigma α lower)) = α
  from (letter-case-final (non-sigma β upper)) = Β
  from (letter-case-final (non-sigma β lower)) = β
  from (letter-case-final (non-sigma γ upper)) = Γ
  from (letter-case-final (non-sigma γ lower)) = γ
  from (letter-case-final (non-sigma δ upper)) = Δ
  from (letter-case-final (non-sigma δ lower)) = δ
  from (letter-case-final (non-sigma ε upper)) = Ε
  from (letter-case-final (non-sigma ε lower)) = ε
  from (letter-case-final (non-sigma ζ upper)) = Ζ
  from (letter-case-final (non-sigma ζ lower)) = ζ
  from (letter-case-final (non-sigma η upper)) = Η
  from (letter-case-final (non-sigma η lower)) = η
  from (letter-case-final (non-sigma θ upper)) = Θ
  from (letter-case-final (non-sigma θ lower)) = θ
  from (letter-case-final (non-sigma ι upper)) = Ι
  from (letter-case-final (non-sigma ι lower)) = ι
  from (letter-case-final (non-sigma κ upper)) = Κ
  from (letter-case-final (non-sigma κ lower)) = κ
  from (letter-case-final (non-sigma ƛ upper)) = Λ
  from (letter-case-final (non-sigma ƛ lower)) = ƛ
  from (letter-case-final (non-sigma μ upper)) = Μ
  from (letter-case-final (non-sigma μ lower)) = μ
  from (letter-case-final (non-sigma ν upper)) = Ν
  from (letter-case-final (non-sigma ν lower)) = ν
  from (letter-case-final (non-sigma ξ upper)) = Ξ
  from (letter-case-final (non-sigma ξ lower)) = ξ
  from (letter-case-final (non-sigma ο upper)) = Ο
  from (letter-case-final (non-sigma ο lower)) = ο
  from (letter-case-final (non-sigma π upper)) = Π
  from (letter-case-final (non-sigma π lower)) = π
  from (letter-case-final (non-sigma ρ upper)) = Ρ
  from (letter-case-final (non-sigma ρ lower)) = ρ
  from (letter-case-final (non-sigma τ upper)) = Τ
  from (letter-case-final (non-sigma τ lower)) = τ
  from (letter-case-final (non-sigma υ upper)) = Υ
  from (letter-case-final (non-sigma υ lower)) = υ
  from (letter-case-final (non-sigma φ upper)) = Φ
  from (letter-case-final (non-sigma φ lower)) = φ
  from (letter-case-final (non-sigma χ upper)) = Χ
  from (letter-case-final (non-sigma χ lower)) = χ
  from (letter-case-final (non-sigma ψ upper)) = Ψ
  from (letter-case-final (non-sigma ψ lower)) = ψ
  from (letter-case-final (non-sigma ω upper)) = Ω
  from (letter-case-final (non-sigma ω lower)) = ω
  from (letter-case-final sigma-upper-n/a) = Σ
  from (letter-case-final sigma-lower-not-final) = σ
  from (letter-case-final sigma-lower-is-final) = ς

  to-from : (x : LetterCaseFinal) → to (from x) ≡ x
  to-from (letter-case-final (non-sigma α upper)) = refl
  to-from (letter-case-final (non-sigma α lower)) = refl
  to-from (letter-case-final (non-sigma β upper)) = refl
  to-from (letter-case-final (non-sigma β lower)) = refl
  to-from (letter-case-final (non-sigma γ upper)) = refl
  to-from (letter-case-final (non-sigma γ lower)) = refl
  to-from (letter-case-final (non-sigma δ upper)) = refl
  to-from (letter-case-final (non-sigma δ lower)) = refl
  to-from (letter-case-final (non-sigma ε upper)) = refl
  to-from (letter-case-final (non-sigma ε lower)) = refl
  to-from (letter-case-final (non-sigma ζ upper)) = refl
  to-from (letter-case-final (non-sigma ζ lower)) = refl
  to-from (letter-case-final (non-sigma η upper)) = refl
  to-from (letter-case-final (non-sigma η lower)) = refl
  to-from (letter-case-final (non-sigma θ upper)) = refl
  to-from (letter-case-final (non-sigma θ lower)) = refl
  to-from (letter-case-final (non-sigma ι upper)) = refl
  to-from (letter-case-final (non-sigma ι lower)) = refl
  to-from (letter-case-final (non-sigma κ upper)) = refl
  to-from (letter-case-final (non-sigma κ lower)) = refl
  to-from (letter-case-final (non-sigma ƛ upper)) = refl
  to-from (letter-case-final (non-sigma ƛ lower)) = refl
  to-from (letter-case-final (non-sigma μ upper)) = refl
  to-from (letter-case-final (non-sigma μ lower)) = refl
  to-from (letter-case-final (non-sigma ν upper)) = refl
  to-from (letter-case-final (non-sigma ν lower)) = refl
  to-from (letter-case-final (non-sigma ξ upper)) = refl
  to-from (letter-case-final (non-sigma ξ lower)) = refl
  to-from (letter-case-final (non-sigma ο upper)) = refl
  to-from (letter-case-final (non-sigma ο lower)) = refl
  to-from (letter-case-final (non-sigma π upper)) = refl
  to-from (letter-case-final (non-sigma π lower)) = refl
  to-from (letter-case-final (non-sigma ρ upper)) = refl
  to-from (letter-case-final (non-sigma ρ lower)) = refl
  to-from (letter-case-final (non-sigma τ upper)) = refl
  to-from (letter-case-final (non-sigma τ lower)) = refl
  to-from (letter-case-final (non-sigma υ upper)) = refl
  to-from (letter-case-final (non-sigma υ lower)) = refl
  to-from (letter-case-final (non-sigma φ upper)) = refl
  to-from (letter-case-final (non-sigma φ lower)) = refl
  to-from (letter-case-final (non-sigma χ upper)) = refl
  to-from (letter-case-final (non-sigma χ lower)) = refl
  to-from (letter-case-final (non-sigma ψ upper)) = refl
  to-from (letter-case-final (non-sigma ψ lower)) = refl
  to-from (letter-case-final (non-sigma ω upper)) = refl
  to-from (letter-case-final (non-sigma ω lower)) = refl
  to-from (letter-case-final sigma-upper-n/a) = refl
  to-from (letter-case-final sigma-lower-not-final) = refl
  to-from (letter-case-final sigma-lower-is-final) = refl

  from-to : (x : ConcreteLetter) → from (to x) ≡ x
  from-to Α = refl
  from-to Β = refl
  from-to Γ = refl
  from-to Δ = refl
  from-to Ε = refl
  from-to Ζ = refl
  from-to Η = refl
  from-to Θ = refl
  from-to Ι = refl
  from-to Κ = refl
  from-to Λ = refl
  from-to Μ = refl
  from-to Ν = refl
  from-to Ξ = refl
  from-to Ο = refl
  from-to Π = refl
  from-to Ρ = refl
  from-to Σ = refl
  from-to Τ = refl
  from-to Υ = refl
  from-to Φ = refl
  from-to Χ = refl
  from-to Ψ = refl
  from-to Ω = refl
  from-to α = refl
  from-to β = refl
  from-to γ = refl
  from-to δ = refl
  from-to ε = refl
  from-to ζ = refl
  from-to η = refl
  from-to θ = refl
  from-to ι = refl
  from-to κ = refl
  from-to ƛ = refl
  from-to μ = refl
  from-to ν = refl
  from-to ξ = refl
  from-to ο = refl
  from-to π = refl
  from-to ρ = refl
  from-to σ = refl
  from-to ς = refl
  from-to τ = refl
  from-to υ = refl
  from-to φ = refl
  from-to χ = refl
  from-to ψ = refl
  from-to ω = refl

abstraction
  : List+ (ConcreteLetter + Mark)
  ≅ List+ (LetterCaseFinal + Mark)
abstraction = over-list+ (over-inl concrete-abstract)

letters-first
  : List+ (LetterCaseFinal + Mark)
  ≅ List+ Mark × List (LetterCaseFinal × List Mark)
  + List+ (LetterCaseFinal × List Mark)
letters-first = group-inr+

infixl 1 _|>_
_|>_ : {A B : Set} → (a : A) → (A → B) → B
_|>_ a f = f a

Βίβλος : List+ (LetterCaseFinal × List Mark)
Βίβλος = "Βίβλος"
  |>> emptiness
  |> _≅_.to abstraction
  |>> letters-first

data Capitalization : Set where
  capitalized uncapitalized : Capitalization

data InvalidCapitalization : Set where
  non-initial-upper : InvalidCapitalization

data LetterFinalD : Letter → Final → Set where
  non-sigma : {l : Letter} → NonSigma l → LetterFinalD l n/a
  sigma-not-final : LetterFinalD σ not-final
  sigma-is-final : LetterFinalD σ is-final

record LetterFinal : Set where
  constructor letter-final
  field
    {letter} : Letter
    {final} : Final
    combo : LetterFinalD letter final

word-capitalization
  : List+ (LetterCaseFinal × List Mark)
  ≅ InvalidCapitalization + Capitalization × List+ (LetterFinal × List Mark)
word-capitalization = {!!}

data InvalidFinal : Set where
  final-in-non-final-position : InvalidFinal
  non-final-in-final-position : InvalidFinal
  final-or-non-final-on-non-sigma : InvalidFinal

finalization
  : Capitalization × List+ (LetterFinal × List Mark)
  ≅ InvalidFinal + Capitalization × List+ (Letter × List Mark)
finalization = {!!}

data Accent : Set where
  acute circumflex : Accent

data Breathing : Set where
  smooth rough : Breathing

data SyllabicMark : Set where
  diaresis iota-subscript : SyllabicMark

Maybe : Set → Set
Maybe A = ⊤ + A

divide-mark
  : Mark
  ≅ Accent + Breathing + SyllabicMark
divide-mark = {!!}

data InvalidMarkCombo : Set where
  double-accent : InvalidMarkCombo
  double-breathing : InvalidMarkCombo
  double-syllabic : InvalidMarkCombo

mark-combos
  : List (Accent + Breathing + SyllabicMark)
  ≅ InvalidMarkCombo + Maybe Accent × Maybe Breathing × Maybe SyllabicMark
mark-combos = {!!}

data OneInvalidMark : Set where

expose-marks
  : Capitalization × List+ (Letter × List Mark)
  ≅ OneInvalidMark + Capitalization × List+ (Letter × Maybe Accent × Maybe Breathing × Maybe SyllabicMark)
expose-marks = {!!}

data Vowel : Set where
  α ε η ι ο υ ω : Vowel
data Consonant : Set where
  β γ δ ζ θ κ ƛ μ ν ξ π ρ σ τ φ χ ψ : Consonant

divide-letter : Letter → Vowel + Consonant
divide-letter = {!!}

distinguish-letter
  : Capitalization × List+ (Letter × Maybe Accent × Maybe Breathing × Maybe SyllabicMark)
  ≅ Capitalization × List+ ((Vowel + Consonant) × Maybe Accent × Maybe Breathing × Maybe SyllabicMark)
distinguish-letter = {!!}

data InvalidConsonantMark : Set where
  accent : InvalidConsonantMark
  syllabic : InvalidConsonantMark
  non-rho-breathing : InvalidConsonantMark

data Consonantῥ : Set where
  consonant : Consonant → Consonantῥ
  ῥ : Consonantῥ

data OneInvalidConsonantMark : Set where

consonant-marks
  : Capitalization × List+ ((Vowel + Consonant) × Maybe Accent × Maybe Breathing × Maybe SyllabicMark)
  ≅ OneInvalidConsonantMark + Capitalization × List+ (Vowel × Maybe Accent × Maybe Breathing × Maybe SyllabicMark + Consonantῥ)
consonant-marks = {!!}

data Diphthong : Set where
  αι αυ ει ευ ηυ οι ου υι : Diphthong

data IotaSubscriptVowel : Set where
  ᾳ ῃ ῳ : IotaSubscriptVowel

VocalicSyllable : Set
VocalicSyllable = Vowel + Diphthong + IotaSubscriptVowel

data InvalidVowelSequence : Set where
  single-vowel++iota/upsilon-no-diaeresis : InvalidVowelSequence

diphthongize
  : Capitalization × List+ (Vowel × Maybe Accent × Maybe Breathing × Maybe SyllabicMark + Consonantῥ)
  ≅ InvalidVowelSequence + Capitalization × List+ (VocalicSyllable × Maybe Accent × Maybe Breathing + Consonantῥ)
diphthongize = {!!}

data NoSyllable : Set where

one-syllable
  : Capitalization × List+ (VocalicSyllable × Maybe Accent × Maybe Breathing + Consonantῥ)
  ≅ NoSyllable + Capitalization × List+ (List Consonantῥ × VocalicSyllable × Maybe Accent × Maybe Breathing) × List Consonantῥ
one-syllable = {!!}

data InvalidBreathing : Set where
  non-initial-vowel-breathing : InvalidBreathing
  non-initial-rho-breathing : InvalidBreathing

data InitialConsonant : Set where
  H β γ δ ζ θ κ ƛ μ ν ξ π ῥ σ τ φ χ ψ : InitialConsonant

breathe
  : Capitalization × List+ (List Consonantῥ × VocalicSyllable × Maybe Accent × Maybe Breathing) × List Consonantῥ
  ≅ InvalidBreathing
    + Capitalization
    × InitialConsonant × VocalicSyllable × Maybe Accent
    × List (Consonant × VocalicSyllable × Maybe Accent)
    × List Consonant
breathe = {!!}

data InvalidAccent : Set where
  two-accents : InvalidAccent
  no-accent? : InvalidAccent
  initial-syllables : InvalidAccent
  circumflex-antepenult : InvalidAccent

data WordAccent : Set where
  oxytone : WordAccent -- acute ultima
  paroxytone : WordAccent -- acute penult
  proparoxytone : WordAccent -- acute antepenult
  perispomenon : WordAccent -- circumflex ultima
  properispomenon : WordAccent -- circumflex penult

accentualize
  : Capitalization
    × InitialConsonant × VocalicSyllable × Maybe Accent
    × List (Consonant × VocalicSyllable × Maybe Accent)
    × List Consonant
  ≅ InvalidAccent
    + Capitalization
    × WordAccent
    × InitialConsonant × VocalicSyllable
    × List (Consonant × VocalicSyllable)
    × List Consonant
accentualize = {!!}
