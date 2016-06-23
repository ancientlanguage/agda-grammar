module Greek.Script where

module Concrete where
  data Letter : Set where
    Α Β Γ Δ Ε Ζ Η Θ Ι Κ Λ Μ Ν Ξ Ο Π Ρ Σ Τ Υ Φ Χ Ψ Ω α β γ δ ε ζ η θ ι κ ƛ μ ν ξ ο π ρ σ ς τ υ φ χ ψ ω : Letter

data Mark : Set where
  acute grave circumflex smooth rough diaeresis iota-sub : Mark

data Punctuation : Set where
  comma mid-dot semicolon period left-paren right-paren em-dash : Punctuation

data Script : Set where
  letter : Concrete.Letter → Script
  mark : Mark → Script
  punctuation : Punctuation → Script
