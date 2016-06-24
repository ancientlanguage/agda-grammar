module Greek.Script where

module Concrete where
  data Letter : Set where
    Α Β Γ Δ Ε Ζ Η Θ Ι Κ Λ Μ Ν Ξ Ο Π Ρ Σ Τ Υ Φ Χ Ψ Ω α β γ δ ε ζ η θ ι κ ƛ μ ν ξ ο π ρ σ ς τ υ φ χ ψ ω : Letter

data Mark : Set where
  acute grave circumflex smooth rough diaeresis iota-sub : Mark

data Punctuation : Set where
  comma mid-dot semicolon period left-paren right-paren em-dash right-single-quote : Punctuation

data Script : Set where
  letter : Concrete.Letter → Script
  mark : Mark → Script
  punctuation : Punctuation → Script

data NonPunctuation : Set where
  letter : Concrete.Letter → NonPunctuation
  mark : Mark → NonPunctuation

module Equivalences where
  import Core
  open Core.Sum
  open Core.Equivalence

  script/punctuation : Script ≅ (Punctuation ⊕ NonPunctuation)
  script/punctuation = equivalence there back left right
    where
    there : Script → Punctuation ⊕ NonPunctuation
    there (letter x) = inr (letter x)
    there (mark x) = inr (mark x)
    there (punctuation x) = inl x
    back : Punctuation ⊕ NonPunctuation → Script
    back (inl a) = punctuation a
    back (inr (letter x)) = letter x
    back (inr (mark x)) = mark x
    left : (x : Script) → back (there x) ≡ x
    left (letter x) = refl
    left (mark x) = refl
    left (punctuation x) = refl
    right : (x : Punctuation ⊕ NonPunctuation) → there (back x) ≡ x
    right (inl a) = refl
    right (inr (letter x)) = refl
    right (inr (mark x)) = refl
