module Common.ListFold2 where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Agda.Builtin.Unit
open import Agda.Builtin.Nat

data Vec {ℓ} (A : Set ℓ) : Nat → Set ℓ where
  []
    : Vec A zero
  _∷_
    : ∀ {n}
    → (x : A)
    → (xs : Vec A n)
    → Vec A (suc n)

map
  : ∀ {ℓ₀ ℓ₁}{n}
  → {A : Set ℓ₀} {B : Set ℓ₁}
  → (f : A → B)
  → (Vec A n → Vec B n)
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

data _⊕_ {ℓ₀ ℓ₁} (A : Set ℓ₀) (B : Set ℓ₁) : Set (ℓ₀ ⊔ ℓ₁) where
  inl : A → A ⊕ B
  inr : B → A ⊕ B

record _⊗_ ..{ℓ₀ ℓ₁} (A : Set ℓ₀) (B : Set ℓ₁) : Set (ℓ₀ ⊔ ℓ₁) where
  constructor _,_
  field
    fst : A
    snd : B
open _⊗_ public

data Case : Set where
  upper lower : Case

data Letter : Set where
  a b c : Letter

data Cap : Set where
  uncap cap : Cap

data CapError : Set where
  upperTail : CapError

parseLower
  : {la : Level}
  → {A : Set la}
  → {n : Nat}
  → Vec (Case ⊗ A) n
  → CapError ⊕ ⊤
parseLower [] = inr _
parseLower ((upper , snd) ∷ xs) = inl upperTail
parseLower ((lower , snd) ∷ xs) = parseLower xs

parseCap
  : {lx : Level}
  → {A : Set lx}
  → {n : Nat}
  → Vec (Case ⊗ A) (suc n)
  → CapError ⊕ Cap
parseCap ((fst , snd) ∷ xs) with parseLower xs
parseCap ((fst , snd) ∷ xs) | inl upperTail = inl upperTail
parseCap ((upper , snd) ∷ xs) | inr x = inr cap
parseCap ((lower , snd) ∷ xs) | inr x = inr uncap

extractCap
  : {la : Level}
  → {A : Set la}
  → {n : Nat}
  → Vec (Case ⊗ A) (suc n)
  → CapError ⊕ (Cap ⊗ Vec A (suc n))
extractCap xs with parseCap xs
extractCap xs | inl e = inl e
extractCap xs | inr x = inr (x , map snd xs)

makeLower
  : {la : Level}
  → {A : Set la}
  → {n : Nat}
  → Vec A n
  → Vec (Case ⊗ A) n
makeLower [] = []
makeLower (x ∷ xs) = (lower , x) ∷ makeLower xs

reverseCap
  : {la : Level}
  → {A : Set la}
  → {n : Nat}
  → Cap ⊗ Vec A (suc n)
  → Vec (Case ⊗ A) (suc n)
reverseCap (uncap , (x ∷ xs)) = makeLower (x ∷ xs)
reverseCap (cap , (x ∷ xs)) = (upper , x) ∷ (makeLower xs)

parseLower-makeLower
  : {la : Level}
  → {A : Set la}
  → {n : Nat}
  → (xs : Vec A n)
  → parseLower (makeLower xs) ≡ inr tt
parseLower-makeLower [] = refl
parseLower-makeLower (x ∷ xs) rewrite parseLower-makeLower xs = refl

map-snd-makeLower
  : {la : Level}
  → {A : Set la}
  → {n : Nat}
  → (xs : Vec A n)
  → map snd (makeLower xs) ≡ xs
map-snd-makeLower [] = refl
map-snd-makeLower (x ∷ xs) rewrite map-snd-makeLower xs = refl

capRoundTrip
  : {la : Level}
  → {A : Set la}
  → {n : Nat}
  → (w : Cap ⊗ Vec A (suc n))
  → inr w ≡ extractCap (reverseCap w)
capRoundTrip (uncap , (x ∷ xs))
  rewrite parseLower-makeLower xs
  | map-snd-makeLower xs
  = refl
capRoundTrip (cap , (x ∷ xs))
  rewrite parseLower-makeLower xs
  | map-snd-makeLower xs
  = refl          
