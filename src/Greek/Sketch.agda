module Greek.Sketch where

open import Agda.Builtin.Char
open import Agda.Builtin.Equality
open import Agda.Builtin.String
open import Agda.Builtin.List
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.FromString
open import Agda.Builtin.Unit

infixl 6 _+_
infixl 7 _×_

data ⊥ : Set where
⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

data _+_ (A B : Set) : Set where
  inl : A → A + B
  inr : B → A + B

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

data Pair (A : Set) (B : A → Set) : Set where
  pair : (a : A) → (b : B a) → Pair A B

List∅ : Set
List∅ = ⊤

List+ : Set → Set
List+ A = A × List A

infix 1 _≅_
record _≅_ (A B : Set) : Set where
  constructor equiv
  field
    to : A → B
    from : B → A
    to-from : (x : B) → to (from x) ≡ x
    from-to : (x : A) → from (to x) ≡ x

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

data ConcreteLetter : Set where
  Α Β Γ Δ Ε Ζ Η Θ Ι Κ Λ Μ Ν Ξ Ο Π Ρ Σ Τ Υ Φ Χ Ψ Ω α β γ δ ε ζ η θ ι κ ƛ μ ν ξ ο π ρ σ ς τ υ φ χ ψ ω : ConcreteLetter
data Mark : Set where
  acute grave circumflex smooth rough diaeresis iota-sub : Mark
data Letter : Set where
  α β γ δ ε ζ η θ ι κ ƛ μ ν ξ ο π ρ σ τ υ φ χ ψ ω : Letter
data LetterCase : Set where
  upper lower : LetterCase
data Final : Set where
  n/a is-final not-final : Final

data LetterCaseFinalD : Letter → LetterCase → Final → Set where
  α : (c : LetterCase) → LetterCaseFinalD α c n/a
  β : (c : LetterCase) → LetterCaseFinalD β c n/a
  γ : (c : LetterCase) → LetterCaseFinalD γ c n/a
  δ : (c : LetterCase) → LetterCaseFinalD δ c n/a
  ε : (c : LetterCase) → LetterCaseFinalD ε c n/a
  ζ : (c : LetterCase) → LetterCaseFinalD ζ c n/a
  η : (c : LetterCase) → LetterCaseFinalD η c n/a
  θ : (c : LetterCase) → LetterCaseFinalD θ c n/a
  ι : (c : LetterCase) → LetterCaseFinalD ι c n/a
  κ : (c : LetterCase) → LetterCaseFinalD κ c n/a
  ƛ : (c : LetterCase) → LetterCaseFinalD ƛ c n/a
  μ : (c : LetterCase) → LetterCaseFinalD μ c n/a
  ν : (c : LetterCase) → LetterCaseFinalD ν c n/a
  ξ : (c : LetterCase) → LetterCaseFinalD ξ c n/a
  ο : (c : LetterCase) → LetterCaseFinalD ο c n/a
  π : (c : LetterCase) → LetterCaseFinalD π c n/a
  ρ : (c : LetterCase) → LetterCaseFinalD ρ c n/a
  τ : (c : LetterCase) → LetterCaseFinalD τ c n/a
  υ : (c : LetterCase) → LetterCaseFinalD υ c n/a
  φ : (c : LetterCase) → LetterCaseFinalD φ c n/a
  χ : (c : LetterCase) → LetterCaseFinalD χ c n/a
  ψ : (c : LetterCase) → LetterCaseFinalD ψ c n/a
  ω : (c : LetterCase) → LetterCaseFinalD ω c n/a
  Σ : LetterCaseFinalD σ upper n/a
  σ : LetterCaseFinalD σ lower not-final
  ς : LetterCaseFinalD σ lower is-final

record LetterCaseFinal : Set where
  constructor letter-case-final
  field
    {letter} : Letter
    {case} : LetterCase
    {final} : Final
    combo : LetterCaseFinalD letter case final

non-empty
  : List (ConcreteLetter + Mark)
  ≅ List∅ + List+ (ConcreteLetter + Mark)
non-empty = emptiness

concrete-abstract
  : ConcreteLetter
  ≅ LetterCaseFinal
concrete-abstract = equiv to from to-from from-to
  where
  to : ConcreteLetter → LetterCaseFinal
  to Α = letter-case-final (α upper)
  to Β = letter-case-final (β upper)
  to Γ = letter-case-final (γ upper)
  to Δ = letter-case-final (δ upper)
  to Ε = letter-case-final (ε upper)
  to Ζ = letter-case-final (ζ upper)
  to Η = letter-case-final (η upper)
  to Θ = letter-case-final (θ upper)
  to Ι = letter-case-final (ι upper)
  to Κ = letter-case-final (κ upper)
  to Λ = letter-case-final (ƛ upper)
  to Μ = letter-case-final (μ upper)
  to Ν = letter-case-final (ν upper)
  to Ξ = letter-case-final (ξ upper)
  to Ο = letter-case-final (ο upper)
  to Π = letter-case-final (π upper)
  to Ρ = letter-case-final (ρ upper)
  to Σ = letter-case-final Σ
  to Τ = letter-case-final (τ upper)
  to Υ = letter-case-final (υ upper)
  to Φ = letter-case-final (φ upper)
  to Χ = letter-case-final (χ upper)
  to Ψ = letter-case-final (ψ upper)
  to Ω = letter-case-final (ω upper)
  to α = letter-case-final (α lower)
  to β = letter-case-final (β lower)
  to γ = letter-case-final (γ lower)
  to δ = letter-case-final (δ lower)
  to ε = letter-case-final (ε lower)
  to ζ = letter-case-final (ζ lower)
  to η = letter-case-final (η lower)
  to θ = letter-case-final (θ lower)
  to ι = letter-case-final (ι lower)
  to κ = letter-case-final (κ lower)
  to ƛ = letter-case-final (ƛ lower)
  to μ = letter-case-final (μ lower)
  to ν = letter-case-final (ν lower)
  to ξ = letter-case-final (ξ lower)
  to ο = letter-case-final (ο lower)
  to π = letter-case-final (π lower)
  to ρ = letter-case-final (ρ lower)
  to σ = letter-case-final σ
  to ς = letter-case-final ς
  to τ = letter-case-final (τ lower)
  to υ = letter-case-final (υ lower)
  to φ = letter-case-final (φ lower)
  to χ = letter-case-final (χ lower)
  to ψ = letter-case-final (ψ lower)
  to ω = letter-case-final (ω lower)

  from : LetterCaseFinal → ConcreteLetter
  from (letter-case-final (α upper)) = Α
  from (letter-case-final (α lower)) = α
  from (letter-case-final (β upper)) = Β
  from (letter-case-final (β lower)) = β
  from (letter-case-final (γ upper)) = Γ
  from (letter-case-final (γ lower)) = γ
  from (letter-case-final (δ upper)) = Δ
  from (letter-case-final (δ lower)) = δ
  from (letter-case-final (ε upper)) = Ε
  from (letter-case-final (ε lower)) = ε
  from (letter-case-final (ζ upper)) = Ζ
  from (letter-case-final (ζ lower)) = ζ
  from (letter-case-final (η upper)) = Η
  from (letter-case-final (η lower)) = η
  from (letter-case-final (θ upper)) = Θ
  from (letter-case-final (θ lower)) = θ
  from (letter-case-final (ι upper)) = Ι
  from (letter-case-final (ι lower)) = ι
  from (letter-case-final (κ upper)) = Κ
  from (letter-case-final (κ lower)) = κ
  from (letter-case-final (ƛ upper)) = Λ
  from (letter-case-final (ƛ lower)) = ƛ
  from (letter-case-final (μ upper)) = Μ
  from (letter-case-final (μ lower)) = μ
  from (letter-case-final (ν upper)) = Ν
  from (letter-case-final (ν lower)) = ν
  from (letter-case-final (ξ upper)) = Ξ
  from (letter-case-final (ξ lower)) = ξ
  from (letter-case-final (ο upper)) = Ο
  from (letter-case-final (ο lower)) = ο
  from (letter-case-final (π upper)) = Π
  from (letter-case-final (π lower)) = π
  from (letter-case-final (ρ upper)) = Ρ
  from (letter-case-final (ρ lower)) = ρ
  from (letter-case-final (τ upper)) = Τ
  from (letter-case-final (τ lower)) = τ
  from (letter-case-final (υ upper)) = Υ
  from (letter-case-final (υ lower)) = υ
  from (letter-case-final (φ upper)) = Φ
  from (letter-case-final (φ lower)) = φ
  from (letter-case-final (χ upper)) = Χ
  from (letter-case-final (χ lower)) = χ
  from (letter-case-final (ψ upper)) = Ψ
  from (letter-case-final (ψ lower)) = ψ
  from (letter-case-final (ω upper)) = Ω
  from (letter-case-final (ω lower)) = ω
  from (letter-case-final Σ) = Σ
  from (letter-case-final σ) = σ
  from (letter-case-final ς) = ς

  to-from : (x : LetterCaseFinal) → to (from x) ≡ x
  to-from (letter-case-final (α upper)) = refl
  to-from (letter-case-final (α lower)) = refl
  to-from (letter-case-final (β upper)) = refl
  to-from (letter-case-final (β lower)) = refl
  to-from (letter-case-final (γ upper)) = refl
  to-from (letter-case-final (γ lower)) = refl
  to-from (letter-case-final (δ upper)) = refl
  to-from (letter-case-final (δ lower)) = refl
  to-from (letter-case-final (ε upper)) = refl
  to-from (letter-case-final (ε lower)) = refl
  to-from (letter-case-final (ζ upper)) = refl
  to-from (letter-case-final (ζ lower)) = refl
  to-from (letter-case-final (η upper)) = refl
  to-from (letter-case-final (η lower)) = refl
  to-from (letter-case-final (θ upper)) = refl
  to-from (letter-case-final (θ lower)) = refl
  to-from (letter-case-final (ι upper)) = refl
  to-from (letter-case-final (ι lower)) = refl
  to-from (letter-case-final (κ upper)) = refl
  to-from (letter-case-final (κ lower)) = refl
  to-from (letter-case-final (ƛ upper)) = refl
  to-from (letter-case-final (ƛ lower)) = refl
  to-from (letter-case-final (μ upper)) = refl
  to-from (letter-case-final (μ lower)) = refl
  to-from (letter-case-final (ν upper)) = refl
  to-from (letter-case-final (ν lower)) = refl
  to-from (letter-case-final (ξ upper)) = refl
  to-from (letter-case-final (ξ lower)) = refl
  to-from (letter-case-final (ο upper)) = refl
  to-from (letter-case-final (ο lower)) = refl
  to-from (letter-case-final (π upper)) = refl
  to-from (letter-case-final (π lower)) = refl
  to-from (letter-case-final (ρ upper)) = refl
  to-from (letter-case-final (ρ lower)) = refl
  to-from (letter-case-final (τ upper)) = refl
  to-from (letter-case-final (τ lower)) = refl
  to-from (letter-case-final (υ upper)) = refl
  to-from (letter-case-final (υ lower)) = refl
  to-from (letter-case-final (φ upper)) = refl
  to-from (letter-case-final (φ lower)) = refl
  to-from (letter-case-final (χ upper)) = refl
  to-from (letter-case-final (χ lower)) = refl
  to-from (letter-case-final (ψ upper)) = refl
  to-from (letter-case-final (ψ lower)) = refl
  to-from (letter-case-final (ω upper)) = refl
  to-from (letter-case-final (ω lower)) = refl
  to-from (letter-case-final Σ) = refl
  to-from (letter-case-final σ) = refl
  to-from (letter-case-final ς) = refl

  from-to : (x :  ConcreteLetter) → from (to x) ≡ x
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

module Eq where
  id : {A : Set} → A ≅ A
  id = equiv (λ x → x) (λ x → x) (λ _ → refl) (λ _ → refl)

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

abstraction
  : List+ (ConcreteLetter + Mark)
  ≅ List+ (LetterCaseFinal + Mark)
abstraction = over-list+ (over-inl concrete-abstract)

split-list+-sum
  : {A B : Set}
  → List+ (A + B)
  ≅ List+ (A × List B) + List+ (B × List A)
split-list+-sum {A} {B} = equiv to from to-from from-to
  where
  to : List+ (A + B) → List+ (A × List B) + List+ (B × List A)
  to (inl x , xs) = inr {!!}
  to (inr x , xs) = inl {!!}

  from : List+ (A × List B) + List+ (B × List A) → List+ (A + B)
  from (inl (x , xs)) = {!!}
  from (inr (x , xs)) = {!!}

  to-from : (x : List+ (A × List B) + List+ (B × List A)) → to (from x) ≡ x
  to-from x = {!!}

  from-to : (x : List+ (A + B)) → from (to x) ≡ x
  from-to x = {!!}

letters-first
  : List+ (LetterCaseFinal + Mark)
  ≅ List+ (Mark × List LetterCaseFinal) + List+ (LetterCaseFinal × List Mark)
letters-first = swap-sum Eq.∘ split-list+-sum

data Capitalization : Set where
  capitalized uncapitalized : Capitalization

data InvalidCapitalization : Set where
  non-initial-upper : InvalidCapitalization

data LetterFinalD : Letter → Final → Set where
  non-sigma : (l : Letter) → (l ≡ σ → ⊥) → LetterFinalD l n/a
  σ : LetterFinalD σ not-final
  ς : LetterFinalD σ is-final

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
