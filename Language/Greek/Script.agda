module Language.Greek.Script where

data ConcreteLetter : Set where
  Α Β Γ Δ Ε Ζ Η Θ Ι Κ Λ Μ Ν Ξ Ο Π Ρ Σ Τ Υ Φ Χ Ψ Ω α β γ δ ε ζ η θ ι κ λ′ μ ν ξ ο π ρ σ ς τ υ φ χ ψ ω : ConcreteLetter

data ConcreteMark : Set where
  ◌̀ ◌́ ◌̂ ◌̓ ◌̔ ◌̈ ◌ͅ : ConcreteMark