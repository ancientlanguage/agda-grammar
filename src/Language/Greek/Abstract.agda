module Language.Greek.Abstract where

open import Prelude.Maybe

data Letter : Set where
  α β γ δ ε ζ η θ ι κ ƛ μ ν ξ ο π ρ σ τ υ φ χ ψ ω : Letter

data Case : Set where
  uppercase lowercase : Case

data Final : Set where
  isFinal notFinal : Final

data LetterCaseFinalI : Letter → Case → Maybe Final → Set where
  α : (c : Case) → LetterCaseFinalI α c no
  β : (c : Case) → LetterCaseFinalI β c no
  γ : (c : Case) → LetterCaseFinalI γ c no
  δ : (c : Case) → LetterCaseFinalI δ c no
  ε : (c : Case) → LetterCaseFinalI ε c no
  ζ : (c : Case) → LetterCaseFinalI ζ c no
  η : (c : Case) → LetterCaseFinalI η c no
  θ : (c : Case) → LetterCaseFinalI θ c no
  ι : (c : Case) → LetterCaseFinalI ι c no
  κ : (c : Case) → LetterCaseFinalI κ c no
  ƛ : (c : Case) → LetterCaseFinalI ƛ c no
  μ : (c : Case) → LetterCaseFinalI μ c no
  ν : (c : Case) → LetterCaseFinalI ν c no
  ξ : (c : Case) → LetterCaseFinalI ξ c no
  ο : (c : Case) → LetterCaseFinalI ο c no
  π : (c : Case) → LetterCaseFinalI π c no
  ρ : (c : Case) → LetterCaseFinalI ρ c no
  Σ′ : LetterCaseFinalI σ uppercase no
  σ : (f : Final) -> LetterCaseFinalI σ lowercase (so f)
  τ : (c : Case) → LetterCaseFinalI τ c no
  υ : (c : Case) → LetterCaseFinalI υ c no
  φ : (c : Case) → LetterCaseFinalI φ c no
  χ : (c : Case) → LetterCaseFinalI χ c no
  ψ : (c : Case) → LetterCaseFinalI ψ c no
  ω : (c : Case) → LetterCaseFinalI ω c no

record LetterCaseFinal : Set where
  constructor lcf
  field
    {l} : Letter
    {c} : Case
    {f} : Maybe Final
    comboI : LetterCaseFinalI l c f
