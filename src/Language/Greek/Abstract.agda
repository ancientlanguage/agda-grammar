module Language.Greek.Abstract where

open import Prelude.Maybe

data Letter : Set where
  α β γ δ ε ζ η θ ι κ ƛ μ ν ξ ο π ρ σ τ υ φ χ ψ ω : Letter

data Case : Set where
  uppercase lowercase : Case

data Final : Set where
  isFinal notFinal : Final

data ComboI : Letter → Case → Maybe Final → Set where
  α : (c : Case) → ComboI α c no
  β : (c : Case) → ComboI β c no
  γ : (c : Case) → ComboI γ c no
  δ : (c : Case) → ComboI δ c no
  ε : (c : Case) → ComboI ε c no
  ζ : (c : Case) → ComboI ζ c no
  η : (c : Case) → ComboI η c no
  θ : (c : Case) → ComboI θ c no
  ι : (c : Case) → ComboI ι c no
  κ : (c : Case) → ComboI κ c no
  ƛ : (c : Case) → ComboI ƛ c no
  μ : (c : Case) → ComboI μ c no
  ν : (c : Case) → ComboI ν c no
  ξ : (c : Case) → ComboI ξ c no
  ο : (c : Case) → ComboI ο c no
  π : (c : Case) → ComboI π c no
  ρ : (c : Case) → ComboI ρ c no
  Σ′ : ComboI σ uppercase no
  σ : (f : Final) -> ComboI σ lowercase (so f)
  τ : (c : Case) → ComboI τ c no
  υ : (c : Case) → ComboI υ c no
  φ : (c : Case) → ComboI φ c no
  χ : (c : Case) → ComboI χ c no
  ψ : (c : Case) → ComboI ψ c no
  ω : (c : Case) → ComboI ω c no

record Combo : Set where
  constructor combo
  field
    {l} : Letter
    {c} : Case
    {f} : Maybe Final
    comboI : ComboI l c f
