module Language.Greek.Abstract where

open import Prelude.Maybe

data Letter : Set where
  α β γ δ ε ζ η θ ι κ ƛ μ ν ξ ο π ρ σ τ υ φ χ ψ ω : Letter

data Case : Set where
  uppercase lowercase : Case

data Final : Set where
  isFinal notFinal : Final

data Combo : Letter → Case → Maybe Final → Set where
  α : (c : Case) → Combo α c nothing
  β : (c : Case) → Combo β c nothing
  γ : (c : Case) → Combo γ c nothing
  δ : (c : Case) → Combo δ c nothing
  ε : (c : Case) → Combo ε c nothing
  ζ : (c : Case) → Combo ζ c nothing
  η : (c : Case) → Combo η c nothing
  θ : (c : Case) → Combo θ c nothing
  ι : (c : Case) → Combo ι c nothing
  κ : (c : Case) → Combo κ c nothing
  ƛ : (c : Case) → Combo ƛ c nothing
  μ : (c : Case) → Combo μ c nothing
  ν : (c : Case) → Combo ν c nothing
  ξ : (c : Case) → Combo ξ c nothing
  ο : (c : Case) → Combo ο c nothing
  π : (c : Case) → Combo π c nothing
  ρ : (c : Case) → Combo ρ c nothing
  Σ′ : Combo σ uppercase nothing
  σ : (f : Final) -> Combo σ lowercase (just f)
  τ : (c : Case) → Combo τ c nothing
  υ : (c : Case) → Combo υ c nothing
  φ : (c : Case) → Combo φ c nothing
  χ : (c : Case) → Combo χ c nothing
  ψ : (c : Case) → Combo ψ c nothing
  ω : (c : Case) → Combo ω c nothing
