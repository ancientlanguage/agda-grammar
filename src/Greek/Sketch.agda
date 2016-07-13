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
data AbstractLetter : Set where
  α β γ δ ε ζ η θ ι κ ƛ μ ν ξ ο π ρ σ τ υ φ χ ψ ω : AbstractLetter
data LetterCase : Set where
  upper lower : LetterCase
data Final : Set where
  n/a final not-final : Final

non-empty
  : List (ConcreteLetter + Mark)
  ≅ List∅ + List+ (ConcreteLetter + Mark)
non-empty = emptiness

concrete-abstract
  : ConcreteLetter
  ≅ AbstractLetter × LetterCase × Final
concrete-abstract = {!!}

abstraction
  : List+ (ConcreteLetter + Mark)
  ≅ List+ (AbstractLetter × LetterCase × Final + Mark)
abstraction = {!!}

data InitialValue (A : Set) : Set where
  initial-value : InitialValue A

right-sum-follows
  : {A B : Set}
  → List+ (A + B)
  ≅ InitialValue B + List+ (A × List B)
right-sum-follows = {!!}

letters-first
  : List+ (AbstractLetter × LetterCase × Final + Mark)
  ≅ InitialValue Mark + List+ (AbstractLetter × LetterCase × Final × List Mark)
letters-first = {!!}

data Capitalization : Set where
  capitalized uncapitalized : Capitalization

data InvalidCapitalization : Set where
  non-initial-upper : InvalidCapitalization

word-capitalization
  : List+ (AbstractLetter × LetterCase × Final × List Mark)
  ≅ InvalidCapitalization + Capitalization × List+ (AbstractLetter × Final × List Mark)
word-capitalization = {!!}

data InvalidFinal : Set where
  final-in-non-final-position : InvalidFinal
  non-final-in-final-position : InvalidFinal
  final-or-non-final-on-non-sigma : InvalidFinal

finalization
  : Capitalization × List+ (AbstractLetter × Final × List Mark)
  ≅ InvalidFinal + Capitalization × List+ (AbstractLetter × List Mark)
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
  : Capitalization × List+ (AbstractLetter × List Mark)
  ≅ OneInvalidMark + Capitalization × List+ (AbstractLetter × Maybe Accent × Maybe Breathing × Maybe SyllabicMark)
expose-marks = {!!}

data Vowel : Set where
  α ε η ι ο υ ω : Vowel
data Consonant : Set where
  β γ δ ζ θ κ ƛ μ ν ξ π ρ σ τ φ χ ψ : Consonant

divide-letter : AbstractLetter → Vowel + Consonant
divide-letter = {!!}

distinguish-letter
  : Capitalization × List+ (AbstractLetter × Maybe Accent × Maybe Breathing × Maybe SyllabicMark)
  → Capitalization × List+ ((Vowel + Consonant) × Maybe Accent × Maybe Breathing × Maybe SyllabicMark)
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
  → OneInvalidConsonantMark + Capitalization × List+ (Vowel × Maybe Accent × Maybe Breathing × Maybe SyllabicMark + Consonantῥ)
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
  → InvalidVowelSequence + Capitalization × List+ (VocalicSyllable × Maybe Accent × Maybe Breathing + Consonantῥ)
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
    × List+ InitialConsonant × VocalicSyllable × Maybe Accent
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
    × List+ InitialConsonant × VocalicSyllable × Maybe Accent
    × List (Consonant × VocalicSyllable × Maybe Accent)
    × List Consonant
  ≅ InvalidAccent
    + Capitalization
    × WordAccent
    × List+ InitialConsonant × VocalicSyllable
    × List (Consonant × VocalicSyllable)
    × List Consonant
accentualize = {!!}
