module AncientLanguage.Grammar.Greek.Script.Letter where

data Letter : Set where
  α β γ δ ε ζ η θ ι κ ƛ μ ν ξ ο π ρ σ τ υ φ χ ψ ω : Letter

data Case : Set where
  upper lower : Case

data Final : Set where
  n/a-final is-final not-final : Final

data LetterCaseFinal : Letter → Case → Final → Set where
  α : (c : Case) → LetterCaseFinal α c n/a-final
  β : (c : Case) → LetterCaseFinal β c n/a-final
  γ : (c : Case) → LetterCaseFinal γ c n/a-final
  δ : (c : Case) → LetterCaseFinal δ c n/a-final
  ε : (c : Case) → LetterCaseFinal ε c n/a-final
  ζ : (c : Case) → LetterCaseFinal ζ c n/a-final
  η : (c : Case) → LetterCaseFinal η c n/a-final
  θ : (c : Case) → LetterCaseFinal θ c n/a-final
  ι : (c : Case) → LetterCaseFinal ι c n/a-final
  κ : (c : Case) → LetterCaseFinal κ c n/a-final
  ƛ : (c : Case) → LetterCaseFinal ƛ c n/a-final
  μ : (c : Case) → LetterCaseFinal μ c n/a-final
  ν : (c : Case) → LetterCaseFinal ν c n/a-final
  ξ : (c : Case) → LetterCaseFinal ξ c n/a-final
  ο : (c : Case) → LetterCaseFinal ο c n/a-final
  π : (c : Case) → LetterCaseFinal π c n/a-final
  ρ : (c : Case) → LetterCaseFinal ρ c n/a-final
  Σ : LetterCaseFinal σ upper n/a-final
  σ : LetterCaseFinal σ lower is-final
  ς : LetterCaseFinal σ lower not-final
  τ : (c : Case) → LetterCaseFinal τ c n/a-final
  υ : (c : Case) → LetterCaseFinal υ c n/a-final
  φ : (c : Case) → LetterCaseFinal φ c n/a-final
  χ : (c : Case) → LetterCaseFinal χ c n/a-final
  ψ : (c : Case) → LetterCaseFinal ψ c n/a-final
  ω : (c : Case) → LetterCaseFinal ω c n/a-final

record LetterCaseFinalRecord : Set where
  constructor letter-case-final-record
  field
    {letter} : Letter
    {case} : Case
    {final} : Final
    letter-case-final : LetterCaseFinal letter case final
