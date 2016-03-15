module Language.Greek.Abstract where

open import Prelude.Maybe

data Letter : Set where
  α β γ δ ε ζ η θ ι κ ƛ μ ν ξ ο π ρ σ τ υ φ χ ψ ω : Letter

data Case : Set where
  uppercase lowercase : Case

data Final : Set where
  isFinal notFinal : Final

data ComboI : Letter → Case → Maybe Final → Set where
  α : (c : Case) → ComboI α c nothing
  β : (c : Case) → ComboI β c nothing
  γ : (c : Case) → ComboI γ c nothing
  δ : (c : Case) → ComboI δ c nothing
  ε : (c : Case) → ComboI ε c nothing
  ζ : (c : Case) → ComboI ζ c nothing
  η : (c : Case) → ComboI η c nothing
  θ : (c : Case) → ComboI θ c nothing
  ι : (c : Case) → ComboI ι c nothing
  κ : (c : Case) → ComboI κ c nothing
  ƛ : (c : Case) → ComboI ƛ c nothing
  μ : (c : Case) → ComboI μ c nothing
  ν : (c : Case) → ComboI ν c nothing
  ξ : (c : Case) → ComboI ξ c nothing
  ο : (c : Case) → ComboI ο c nothing
  π : (c : Case) → ComboI π c nothing
  ρ : (c : Case) → ComboI ρ c nothing
  Σ′ : ComboI σ uppercase nothing
  σ : (f : Final) -> ComboI σ lowercase (just f)
  τ : (c : Case) → ComboI τ c nothing
  υ : (c : Case) → ComboI υ c nothing
  φ : (c : Case) → ComboI φ c nothing
  χ : (c : Case) → ComboI χ c nothing
  ψ : (c : Case) → ComboI ψ c nothing
  ω : (c : Case) → ComboI ω c nothing

record Combo : Set where
  constructor combo
  field
    {l} : Letter
    {c} : Case
    {f} : Maybe Final
    comboI : ComboI l c f
