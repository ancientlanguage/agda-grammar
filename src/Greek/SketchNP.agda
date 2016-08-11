module Greek.SketchNP where

open import Agda.Builtin.Equality

infixl 7 _×_
infixl 6 _+_
infixl 1 _↔_
infixl 1 _∘_

data ⊥ : Set where
open import Agda.Builtin.Unit

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

data _+_ (A B : Set) : Set where
  inl : A → A + B
  inr : B → A + B

_∘_ : {A B C : Set} → (B → C) → (A → B) → A → C
(f ∘ g) x = f (g x)

open import Agda.Builtin.List
module ListM where
  map : {A B : Set} → (A → B) → List A → List B
  map f [] = []
  map f (x ∷ xs) = f x ∷ map f xs

  _++_ : {A : Set} → (xs ys : List A) → List A
  [] ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

record Applicative (F : Set → Set) : Set1 where
  field
    pure : {A : Set} → A → F A
    ap : {A B : Set} → F (A → B) → F A → F B

module ApplicativeInstance where
  infixl 4 _⊛_
  _⊛_ : {F : Set → Set} → {{X : Applicative F}} → {A B : Set} → F (A → B) → F A → F B
  _⊛_ {{X}} = Applicative.ap X

  pure : {F : Set → Set} → {{X : Applicative F}} → {A : Set} → A → F A
  pure {{X}} = Applicative.pure X

module Lens {F : Set → Set} {{X : Applicative F}} where
  open ApplicativeInstance
  Traversal : (T : Set → Set) → Set1
  Traversal T = {A B : Set} → (A → F B) → T A → F (T B)

--  traverse : {A B : Set} → (A → F B) → List A → F (List B)
  traverse : Traversal List
  traverse f [] = pure []
  traverse f (x ∷ xs) = (pure _∷_) ⊛ (f x) ⊛ (traverse f xs)

--  fstLens : {A B C : Set} → (A → F B) → (A × C) → F (B × C)
  fstLens : {C : Set} → Traversal (_× C)
  fstLens f (fst , snd) = pure (_, snd) ⊛ (f fst)

--  sndLens : {A B C : Set} → (A → F B) → (C × A) → F (C × B)
  sndLens : {C : Set} → Traversal (C ×_)
  sndLens f (fst , snd) = pure (fst ,_) ⊛ (f snd)

--  inlLens : {A B C : Set} → (A → F B) → (A + C) → F (B + C)
  inlLens : {C : Set} → Traversal (_+ C)
  inlLens f (inl x) = pure inl ⊛ f x
  inlLens f (inr x) = pure (inr x)

--  inrLens : {A B C : Set} → (A → F B) → (C + A) → F (C + B)
  inrLens : {C : Set} → Traversal (C +_)
  inrLens f (inl x) = pure (inl x)
  inrLens f (inr x) = pure inr ⊛ f x
open Lens

data Expect (E A : Set) : Set where
  expected : A → Expect E A
  unexpected : List E → Expect E A

pattern unexpected-single x = unexpected (x ∷ [])

module ExpectApplicativeM (E : Set) where
  F : (A : Set) → Set
  F A = Expect E A

  pure : {A : Set} → A → F A
  pure a = expected a

  ap : {A B : Set} → F (A → B) → F A → F B
  ap (expected f) (expected x) = expected (f x)
  ap (expected f) (unexpected e) = unexpected e
  ap (unexpected e) (expected x) = unexpected e
  ap (unexpected e1) (unexpected e2) = unexpected (e1 ListM.++ e2)

instance
  ExpectApplicative : {E : Set} → Applicative (Expect E)
  ExpectApplicative {E} = record { ExpectApplicativeM E }

mapUnexpected : {A E1 E2 : Set} → (E1 → E2) → Expect E1 A → Expect E2 A
mapUnexpected f (expected x) = expected x
mapUnexpected f (unexpected x) = unexpected (ListM.map f x)

module Zero where
  ⊥-elim : {A : Set} → ⊥ → A
  ⊥-elim ()

List∅ : Set
List∅ = ⊤ where open import Agda.Builtin.Unit

List+ : Set → Set
List+ A = A × List A

module ExpectInhabit where
  open Zero
  assume-expected : {A B : Set} → Expect A B → Set
  assume-expected (expected x) = ⊤
  assume-expected (unexpected x) = ⊥

  move-expected : {A B : Set}
    → (x : Expect A B)
    → {p : assume-expected x}
    → B
  move-expected (expected b) = b
  move-expected (unexpected a) {p} = ⊥-elim p

module SumInhabit where
  open Zero
  assume-inr : {A B : Set} → A + B → Set
  assume-inr (inl a) = ⊥
  assume-inr (inr b) = ⊤

  move-inr : {A B : Set}
    → (x : A + B)
    → {p : assume-inr x}
    → B
  move-inr (inl a) {p} = ⊥-elim p
  move-inr (inr b) = b

module ListSum where
  split : {A B : Set} → List (A + B) → List A + List B
  split [] = inr []
  split (x ∷ xs) with split xs
  split (inl a ∷ xs) | inl as = inl (a ∷ as)
  split (inr b ∷ xs) | inl as = inl as
  split (inl a ∷ xs) | inr bs = inl (a ∷ [])
  split (inr b ∷ xs) | inr bs = inr (b ∷ bs)

record ToFrom (A B : Set) : Set where
  field
    to : A → B
    from : B → A

_↔_ : (A B : Set) → Set
_↔_ = ToFrom

record ToFromM (F : Set → Set) (A B : Set) : Set where
  field
    toM : A → F B
    from : B → A

PartialToFrom : {E : Set} → (A B : Set) → Set
PartialToFrom {E} = ToFromM (Expect E)

AmbiguousToFrom : (A B : Set) → Set
AmbiguousToFrom = ToFromM List

Id : {A : Set} → A ↔ A
Id = record { to = id ; from = id } where id = λ x → x

module OverProductM {A B C D : Set} (X : A ↔ B) (Y : C ↔ D) where
  to : A × C → B × D
  to (a , c) = (ToFrom.to X a , ToFrom.to Y c)

  from : B × D → A × C
  from (b , c) = (ToFrom.from X b , ToFrom.from Y c)

OverProduct : {A B C D : Set} → A ↔ B → C ↔ D → A × C ↔ B × D
OverProduct X Y = record { OverProductM X Y }

OverFst : {A B C : Set} → A ↔ B → A × C ↔ B × C
OverFst X = OverProduct X Id

OverSnd : {A B C : Set} → A ↔ B → C × A ↔ C × B
OverSnd X = OverProduct Id X

module OverSumM {A B C D : Set} (X : A ↔ B) (Y : C ↔ D) where
  to : A + C → B + D
  to (inl a) = inl (ToFrom.to X a)
  to (inr c) = inr (ToFrom.to Y c)

  from : B + D → A + C
  from (inl b) = inl (ToFrom.from X b)
  from (inr d) = inr (ToFrom.from Y d)

OverSum : {A B C D : Set} → A ↔ B → C ↔ D → A + C ↔ B + D
OverSum X Y = record { OverSumM X Y }

OverInl : {A B C : Set} → A ↔ B → A + C ↔ B + C
OverInl X = OverSum X Id

OverInr : {A B C : Set} → A ↔ B → C + A ↔ C + B
OverInr X = OverSum Id X

module OverListM {A B : Set} (X : ToFrom A B) where
  to : List A → List B
  to [] = []
  to (x ∷ xs) = ToFrom.to X x ∷ to xs

  from : List B → List A
  from [] = []
  from (x ∷ xs) = ToFrom.from X x ∷ from xs

OverList : {A B : Set} → A ↔ B → List A ↔ List B
OverList X = record { OverListM X }

data ConcreteLetter : Set where
  Α Β Γ Δ Ε Ζ Η Θ Ι Κ Λ Μ Ν Ξ Ο Π Ρ Σ Τ Υ Φ Χ Ψ Ω : ConcreteLetter
  α β γ δ ε ζ η θ ι κ ƛ μ ν ξ ο π ρ σ ς τ υ φ χ ψ ω : ConcreteLetter
data Mark : Set where
  acute grave circumflex : Mark
  smooth rough : Mark
  diaeresis iota-sub : Mark

open import Agda.Builtin.Char using (Char)
data NonGreekChar : Set where
  non-greek-char : Char → NonGreekChar

module UnicodeChar where

  pattern valid-letter x = expected (inl x)
  pattern valid-mark x = expected (inr x)
  pattern invalid-char x = unexpected-single (non-greek-char x)

  from : Char → Expect NonGreekChar (ConcreteLetter + Mark)
  from 'Α' = valid-letter Α
  from 'Β' = valid-letter Β
  from 'Γ' = valid-letter Γ
  from 'Δ' = valid-letter Δ
  from 'Ε' = valid-letter Ε
  from 'Ζ' = valid-letter Ζ
  from 'Η' = valid-letter Η
  from 'Θ' = valid-letter Θ
  from 'Ι' = valid-letter Ι
  from 'Κ' = valid-letter Κ
  from 'Λ' = valid-letter Λ
  from 'Μ' = valid-letter Μ
  from 'Ν' = valid-letter Ν
  from 'Ξ' = valid-letter Ξ
  from 'Ο' = valid-letter Ο
  from 'Π' = valid-letter Π
  from 'Ρ' = valid-letter Ρ
  from 'Σ' = valid-letter Σ
  from 'Τ' = valid-letter Τ
  from 'Υ' = valid-letter Υ
  from 'Φ' = valid-letter Φ
  from 'Χ' = valid-letter Χ
  from 'Ψ' = valid-letter Ψ
  from 'Ω' = valid-letter Ω
  from 'α' = valid-letter α
  from 'β' = valid-letter β
  from 'γ' = valid-letter γ
  from 'δ' = valid-letter δ
  from 'ε' = valid-letter ε
  from 'ζ' = valid-letter ζ
  from 'η' = valid-letter η
  from 'θ' = valid-letter θ
  from 'ι' = valid-letter ι
  from 'κ' = valid-letter κ
  from 'λ' = valid-letter ƛ
  from 'μ' = valid-letter μ
  from 'ν' = valid-letter ν
  from 'ξ' = valid-letter ξ
  from 'ο' = valid-letter ο
  from 'π' = valid-letter π
  from 'ρ' = valid-letter ρ
  from 'σ' = valid-letter σ
  from 'ς' = valid-letter ς
  from 'τ' = valid-letter τ
  from 'υ' = valid-letter υ
  from 'φ' = valid-letter φ
  from 'χ' = valid-letter χ
  from 'ψ' = valid-letter ψ
  from 'ω' = valid-letter ω
  from '\x0300' = valid-mark grave -- COMBINING GRAVE ACCENT
  from '\x0301' = valid-mark acute -- COMBINING ACUTE ACCENT
  from '\x0308' = valid-mark diaeresis -- COMBINING DIAERESIS
  from '\x0313' = valid-mark smooth -- COMBINING COMMA ABOVE
  from '\x0314' = valid-mark rough -- COMBINING REVERSED COMMA ABOVE
  from '\x0342' = valid-mark circumflex -- COMBINING GREEK PERISPOMENI
  from '\x0345' = valid-mark iota-sub -- COMBINING GREEK YPOGEGRAMMENI
  from x = invalid-char x

  pattern letter x = inl x
  pattern mark x = inr x

  to : ConcreteLetter + Mark → Char
  to (letter Α) = 'Α'
  to (letter Β) = 'Β'
  to (letter Γ) = 'Γ'
  to (letter Δ) = 'Δ'
  to (letter Ε) = 'Ε'
  to (letter Ζ) = 'Ζ'
  to (letter Η) = 'Η'
  to (letter Θ) = 'Θ'
  to (letter Ι) = 'Ι'
  to (letter Κ) = 'Κ'
  to (letter Λ) = 'Λ'
  to (letter Μ) = 'Μ'
  to (letter Ν) = 'Ν'
  to (letter Ξ) = 'Ξ'
  to (letter Ο) = 'Ο'
  to (letter Π) = 'Π'
  to (letter Ρ) = 'Ρ'
  to (letter Σ) = 'Σ'
  to (letter Τ) = 'Τ'
  to (letter Υ) = 'Υ'
  to (letter Φ) = 'Φ'
  to (letter Χ) = 'Χ'
  to (letter Ψ) = 'Ψ'
  to (letter Ω) = 'Ω'
  to (letter α) = 'α'
  to (letter β) = 'β'
  to (letter γ) = 'γ'
  to (letter δ) = 'δ'
  to (letter ε) = 'ε'
  to (letter ζ) = 'ζ'
  to (letter η) = 'η'
  to (letter θ) = 'θ'
  to (letter ι) = 'ι'
  to (letter κ) = 'κ'
  to (letter ƛ) = 'λ'
  to (letter μ) = 'μ'
  to (letter ν) = 'ν'
  to (letter ξ) = 'ξ'
  to (letter ο) = 'ο'
  to (letter π) = 'π'
  to (letter ρ) = 'ρ'
  to (letter σ) = 'σ'
  to (letter ς) = 'ς'
  to (letter τ) = 'τ'
  to (letter υ) = 'υ'
  to (letter φ) = 'φ'
  to (letter χ) = 'χ'
  to (letter ψ) = 'ψ'
  to (letter ω) = 'ω'
  to (mark grave) = '\x0300' -- COMBINING GRAVE ACCENT
  to (mark acute) = '\x0301' -- COMBINING ACUTE ACCENT
  to (mark diaeresis) = '\x0308' -- COMBINING DIAERESIS
  to (mark smooth) = '\x0313' -- COMBINING COMMA ABOVE
  to (mark rough) = '\x0314' -- COMBINING REVERSED COMMA ABOVE
  to (mark circumflex) = '\x0342' -- COMBINING GREEK PERISPOMENI
  to (mark iota-sub) = '\x0345' -- COMBINING GREEK YPOGEGRAMMENI

module UnicodeString where
  open import Agda.Builtin.FromString
  open import Agda.Builtin.String
  open import Unicode.Decompose
  from-any : String → Expect NonGreekChar (List (ConcreteLetter + Mark))
  from-any xs = traverse UnicodeChar.from (primStringToList (decompose xs))

  from
    : (xs : String)
    → {{p : ExpectInhabit.assume-expected (from-any xs)}}
    → List (ConcreteLetter + Mark)
  from xs {{p}} = ExpectInhabit.move-expected (from-any xs) {p = p}

  instance
    StringScript : IsString (List (ConcreteLetter + Mark))
    IsString.Constraint StringScript xs = ExpectInhabit.assume-expected (from-any xs)
    IsString.fromString StringScript xs = from xs

  instance
    StringString : IsString String
    IsString.Constraint StringString xs = ⊤
    IsString.fromString StringString xs = xs

  to
    : List (ConcreteLetter + Mark)
    → String
  to xs = primStringFromList (ListM.map UnicodeChar.to xs)

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

module AbstractLetterM where
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

AbstractLetter : ConcreteLetter ↔ LetterCaseFinal
AbstractLetter = record { AbstractLetterM }

module GreekWords where
  open import Unicode.Decompose
  open import Agda.Builtin.String

  Word : List (ConcreteLetter + Mark) ↔ List (LetterCaseFinal + Mark)
  Word = OverList (OverSum AbstractLetter Id)

  Script = List (ConcreteLetter + Mark)
  Βίβλος : Script
  Βίβλος = "Βίβλος"

  ΒίβλοςT : List (LetterCaseFinal + Mark)
  ΒίβλοςT = ToFrom.to Word "Βίβλος"

  test1 : decompose "Βίβλος" ≡ UnicodeString.to Βίβλος
  test1 = refl
