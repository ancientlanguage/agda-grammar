module Language.Greek.ConcreteCombined where

open import Agda.Builtin.Equality
open import Prelude.Monoidal.Coproduct
open import Common.RoundTrip
open import Language.Greek.Concrete

open ⊕
  using (inl)
  using (inr)

letterOrMark : Combined → Letter ⊕ Mark
letterOrMark Α = inl Α
letterOrMark Β = inl Β
letterOrMark Γ = inl Γ
letterOrMark Δ = inl Δ
letterOrMark Ε = inl Ε
letterOrMark Ζ = inl Ζ
letterOrMark Η = inl Η
letterOrMark Θ = inl Θ
letterOrMark Ι = inl Ι
letterOrMark Κ = inl Κ
letterOrMark Λ = inl Λ
letterOrMark Μ = inl Μ
letterOrMark Ν = inl Ν
letterOrMark Ξ = inl Ξ
letterOrMark Ο = inl Ο
letterOrMark Π = inl Π
letterOrMark Ρ = inl Ρ
letterOrMark Σ′ = inl Σ′
letterOrMark Τ = inl Τ
letterOrMark Υ = inl Υ
letterOrMark Φ = inl Φ
letterOrMark Χ = inl Χ
letterOrMark Ψ = inl Ψ
letterOrMark Ω = inl Ω
letterOrMark α = inl α
letterOrMark β = inl β
letterOrMark γ = inl γ
letterOrMark δ = inl δ
letterOrMark ε = inl ε
letterOrMark ζ = inl ζ
letterOrMark η = inl η
letterOrMark θ = inl θ
letterOrMark ι = inl ι
letterOrMark κ = inl κ
letterOrMark ƛ = inl ƛ
letterOrMark μ = inl μ
letterOrMark ν = inl ν
letterOrMark ξ = inl ξ
letterOrMark ο = inl ο
letterOrMark π = inl π
letterOrMark ρ = inl ρ
letterOrMark σ = inl σ
letterOrMark ς = inl ς
letterOrMark τ = inl τ
letterOrMark υ = inl υ
letterOrMark φ = inl φ
letterOrMark χ = inl χ
letterOrMark ψ = inl ψ
letterOrMark ω = inl ω
letterOrMark acute = inr acute
letterOrMark grave = inr grave
letterOrMark circumflex = inr circumflex
letterOrMark smooth = inr smooth
letterOrMark rough = inr rough
letterOrMark diaeresis = inr diaeresis
letterOrMark iotaSubscript = inr iotaSubscript

letterOrMarkInv : Letter ⊕ Mark → Combined
letterOrMarkInv (inl Α) = Α
letterOrMarkInv (inl Β) = Β
letterOrMarkInv (inl Γ) = Γ
letterOrMarkInv (inl Δ) = Δ
letterOrMarkInv (inl Ε) = Ε
letterOrMarkInv (inl Ζ) = Ζ
letterOrMarkInv (inl Η) = Η
letterOrMarkInv (inl Θ) = Θ
letterOrMarkInv (inl Ι) = Ι
letterOrMarkInv (inl Κ) = Κ
letterOrMarkInv (inl Λ) = Λ
letterOrMarkInv (inl Μ) = Μ
letterOrMarkInv (inl Ν) = Ν
letterOrMarkInv (inl Ξ) = Ξ
letterOrMarkInv (inl Ο) = Ο
letterOrMarkInv (inl Π) = Π
letterOrMarkInv (inl Ρ) = Ρ
letterOrMarkInv (inl Σ′) = Σ′
letterOrMarkInv (inl Τ) = Τ
letterOrMarkInv (inl Υ) = Υ
letterOrMarkInv (inl Φ) = Φ
letterOrMarkInv (inl Χ) = Χ
letterOrMarkInv (inl Ψ) = Ψ
letterOrMarkInv (inl Ω) = Ω
letterOrMarkInv (inl α) = α
letterOrMarkInv (inl β) = β
letterOrMarkInv (inl γ) = γ
letterOrMarkInv (inl δ) = δ
letterOrMarkInv (inl ε) = ε
letterOrMarkInv (inl ζ) = ζ
letterOrMarkInv (inl η) = η
letterOrMarkInv (inl θ) = θ
letterOrMarkInv (inl ι) = ι
letterOrMarkInv (inl κ) = κ
letterOrMarkInv (inl ƛ) = ƛ
letterOrMarkInv (inl μ) = μ
letterOrMarkInv (inl ν) = ν
letterOrMarkInv (inl ξ) = ξ
letterOrMarkInv (inl ο) = ο
letterOrMarkInv (inl π) = π
letterOrMarkInv (inl ρ) = ρ
letterOrMarkInv (inl σ) = σ
letterOrMarkInv (inl ς) = ς
letterOrMarkInv (inl τ) = τ
letterOrMarkInv (inl υ) = υ
letterOrMarkInv (inl φ) = φ
letterOrMarkInv (inl χ) = χ
letterOrMarkInv (inl ψ) = ψ
letterOrMarkInv (inl ω) = ω
letterOrMarkInv (inr acute) = acute
letterOrMarkInv (inr grave) = grave
letterOrMarkInv (inr circumflex) = circumflex
letterOrMarkInv (inr smooth) = smooth
letterOrMarkInv (inr rough) = rough
letterOrMarkInv (inr diaeresis) = diaeresis
letterOrMarkInv (inr iotaSubscript) = iotaSubscript

letterOrMarkEquivP : (x : Letter ⊕ Mark) → x ≡ letterOrMark (letterOrMarkInv x)
letterOrMarkEquivP (inl Α) = refl
letterOrMarkEquivP (inl Β) = refl
letterOrMarkEquivP (inl Γ) = refl
letterOrMarkEquivP (inl Δ) = refl
letterOrMarkEquivP (inl Ε) = refl
letterOrMarkEquivP (inl Ζ) = refl
letterOrMarkEquivP (inl Η) = refl
letterOrMarkEquivP (inl Θ) = refl
letterOrMarkEquivP (inl Ι) = refl
letterOrMarkEquivP (inl Κ) = refl
letterOrMarkEquivP (inl Λ) = refl
letterOrMarkEquivP (inl Μ) = refl
letterOrMarkEquivP (inl Ν) = refl
letterOrMarkEquivP (inl Ξ) = refl
letterOrMarkEquivP (inl Ο) = refl
letterOrMarkEquivP (inl Π) = refl
letterOrMarkEquivP (inl Ρ) = refl
letterOrMarkEquivP (inl Σ′) = refl
letterOrMarkEquivP (inl Τ) = refl
letterOrMarkEquivP (inl Υ) = refl
letterOrMarkEquivP (inl Φ) = refl
letterOrMarkEquivP (inl Χ) = refl
letterOrMarkEquivP (inl Ψ) = refl
letterOrMarkEquivP (inl Ω) = refl
letterOrMarkEquivP (inl α) = refl
letterOrMarkEquivP (inl β) = refl
letterOrMarkEquivP (inl γ) = refl
letterOrMarkEquivP (inl δ) = refl
letterOrMarkEquivP (inl ε) = refl
letterOrMarkEquivP (inl ζ) = refl
letterOrMarkEquivP (inl η) = refl
letterOrMarkEquivP (inl θ) = refl
letterOrMarkEquivP (inl ι) = refl
letterOrMarkEquivP (inl κ) = refl
letterOrMarkEquivP (inl ƛ) = refl
letterOrMarkEquivP (inl μ) = refl
letterOrMarkEquivP (inl ν) = refl
letterOrMarkEquivP (inl ξ) = refl
letterOrMarkEquivP (inl ο) = refl
letterOrMarkEquivP (inl π) = refl
letterOrMarkEquivP (inl ρ) = refl
letterOrMarkEquivP (inl σ) = refl
letterOrMarkEquivP (inl ς) = refl
letterOrMarkEquivP (inl τ) = refl
letterOrMarkEquivP (inl υ) = refl
letterOrMarkEquivP (inl φ) = refl
letterOrMarkEquivP (inl χ) = refl
letterOrMarkEquivP (inl ψ) = refl
letterOrMarkEquivP (inl ω) = refl
letterOrMarkEquivP (inr acute) = refl
letterOrMarkEquivP (inr grave) = refl
letterOrMarkEquivP (inr circumflex) = refl
letterOrMarkEquivP (inr smooth) = refl
letterOrMarkEquivP (inr rough) = refl
letterOrMarkEquivP (inr diaeresis) = refl
letterOrMarkEquivP (inr iotaSubscript) = refl

letterOrMarkEquiv : Combined ⟳ Letter ⊕ Mark
letterOrMarkEquiv = equiv letterOrMark letterOrMarkInv letterOrMarkEquivP
