module Language.Greek.AbstractConcrete where

open import Agda.Builtin.Equality
open import Prelude.Product
open import Prelude.Maybe
open import Common.Equiv
open import Language.Greek.Concrete renaming (Letter to ConcreteLetter)
open import Language.Greek.Abstract renaming (Letter to AbstractLetter)

abstractLetter : ConcreteLetter → Combo
abstractLetter Α = combo (α uppercase)
abstractLetter Β = combo (β uppercase)
abstractLetter Γ = combo (γ uppercase)
abstractLetter Δ = combo (δ uppercase)
abstractLetter Ε = combo (ε uppercase)
abstractLetter Ζ = combo (ζ uppercase)
abstractLetter Η = combo (η uppercase)
abstractLetter Θ = combo (θ uppercase)
abstractLetter Ι = combo (ι uppercase)
abstractLetter Κ = combo (κ uppercase)
abstractLetter Λ = combo (ƛ uppercase)
abstractLetter Μ = combo (μ uppercase)
abstractLetter Ν = combo (ν uppercase)
abstractLetter Ξ = combo (ξ uppercase)
abstractLetter Ο = combo (ο uppercase)
abstractLetter Π = combo (π uppercase)
abstractLetter Ρ = combo (ρ uppercase)
abstractLetter Σ′ = combo Σ′
abstractLetter Τ = combo (τ uppercase)
abstractLetter Υ = combo (υ uppercase)
abstractLetter Φ = combo (φ uppercase)
abstractLetter Χ = combo (χ uppercase)
abstractLetter Ψ = combo (ψ uppercase)
abstractLetter Ω = combo (ω uppercase)
abstractLetter α = combo (α lowercase)
abstractLetter β = combo (β lowercase)
abstractLetter γ = combo (γ lowercase)
abstractLetter δ = combo (δ lowercase)
abstractLetter ε = combo (ε lowercase)
abstractLetter ζ = combo (ζ lowercase)
abstractLetter η = combo (η lowercase)
abstractLetter θ = combo (θ lowercase)
abstractLetter ι = combo (ι lowercase)
abstractLetter κ = combo (κ lowercase)
abstractLetter ƛ = combo (ƛ lowercase)
abstractLetter μ = combo (μ lowercase)
abstractLetter ν = combo (ν lowercase)
abstractLetter ξ = combo (ξ lowercase)
abstractLetter ο = combo (ο lowercase)
abstractLetter π = combo (π lowercase)
abstractLetter ρ = combo (ρ lowercase)
abstractLetter σ = combo (σ notFinal)
abstractLetter ς = combo (σ isFinal)
abstractLetter τ = combo (τ lowercase)
abstractLetter υ = combo (υ lowercase)
abstractLetter φ = combo (φ lowercase)
abstractLetter χ = combo (χ lowercase)
abstractLetter ψ = combo (ψ lowercase)
abstractLetter ω = combo (ω lowercase)

abstractLetterInv : Combo → ConcreteLetter
abstractLetterInv (combo (α uppercase)) = Α
abstractLetterInv (combo (α lowercase)) = α
abstractLetterInv (combo (β uppercase)) = Β
abstractLetterInv (combo (β lowercase)) = β
abstractLetterInv (combo (γ uppercase)) = Γ
abstractLetterInv (combo (γ lowercase)) = γ
abstractLetterInv (combo (δ uppercase)) = Δ
abstractLetterInv (combo (δ lowercase)) = δ
abstractLetterInv (combo (ε uppercase)) = Ε
abstractLetterInv (combo (ε lowercase)) = ε
abstractLetterInv (combo (ζ uppercase)) = Ζ
abstractLetterInv (combo (ζ lowercase)) = ζ
abstractLetterInv (combo (η uppercase)) = Η
abstractLetterInv (combo (η lowercase)) = η
abstractLetterInv (combo (θ uppercase)) = Θ
abstractLetterInv (combo (θ lowercase)) = θ
abstractLetterInv (combo (ι uppercase)) = Ι
abstractLetterInv (combo (ι lowercase)) = ι
abstractLetterInv (combo (κ uppercase)) = Κ
abstractLetterInv (combo (κ lowercase)) = κ
abstractLetterInv (combo (ƛ uppercase)) = Λ
abstractLetterInv (combo (ƛ lowercase)) = ƛ
abstractLetterInv (combo (μ uppercase)) = Μ
abstractLetterInv (combo (μ lowercase)) = μ
abstractLetterInv (combo (ν uppercase)) = Ν
abstractLetterInv (combo (ν lowercase)) = ν
abstractLetterInv (combo (ξ uppercase)) = Ξ
abstractLetterInv (combo (ξ lowercase)) = ξ
abstractLetterInv (combo (ο uppercase)) = Ο
abstractLetterInv (combo (ο lowercase)) = ο
abstractLetterInv (combo (π uppercase)) = Π
abstractLetterInv (combo (π lowercase)) = π
abstractLetterInv (combo (ρ uppercase)) = Ρ
abstractLetterInv (combo (ρ lowercase)) = ρ
abstractLetterInv (combo Σ′) = Σ′
abstractLetterInv (combo (σ notFinal)) = σ
abstractLetterInv (combo (σ isFinal)) = ς
abstractLetterInv (combo (τ uppercase)) = Τ
abstractLetterInv (combo (τ lowercase)) = τ
abstractLetterInv (combo (υ uppercase)) = Υ
abstractLetterInv (combo (υ lowercase)) = υ
abstractLetterInv (combo (φ uppercase)) = Φ
abstractLetterInv (combo (φ lowercase)) = φ
abstractLetterInv (combo (χ uppercase)) = Χ
abstractLetterInv (combo (χ lowercase)) = χ
abstractLetterInv (combo (ψ uppercase)) = Ψ
abstractLetterInv (combo (ψ lowercase)) = ψ
abstractLetterInv (combo (ω uppercase)) = Ω
abstractLetterInv (combo (ω lowercase)) = ω

abstractLetterEquivP : (c : Combo) → c ≡ (abstractLetter (abstractLetterInv c))
abstractLetterEquivP (combo (α uppercase)) = refl
abstractLetterEquivP (combo (α lowercase)) = refl
abstractLetterEquivP (combo (β uppercase)) = refl
abstractLetterEquivP (combo (β lowercase)) = refl
abstractLetterEquivP (combo (γ uppercase)) = refl
abstractLetterEquivP (combo (γ lowercase)) = refl
abstractLetterEquivP (combo (δ uppercase)) = refl
abstractLetterEquivP (combo (δ lowercase)) = refl
abstractLetterEquivP (combo (ε uppercase)) = refl
abstractLetterEquivP (combo (ε lowercase)) = refl
abstractLetterEquivP (combo (ζ uppercase)) = refl
abstractLetterEquivP (combo (ζ lowercase)) = refl
abstractLetterEquivP (combo (η uppercase)) = refl
abstractLetterEquivP (combo (η lowercase)) = refl
abstractLetterEquivP (combo (θ uppercase)) = refl
abstractLetterEquivP (combo (θ lowercase)) = refl
abstractLetterEquivP (combo (ι uppercase)) = refl
abstractLetterEquivP (combo (ι lowercase)) = refl
abstractLetterEquivP (combo (κ uppercase)) = refl
abstractLetterEquivP (combo (κ lowercase)) = refl
abstractLetterEquivP (combo (ƛ uppercase)) = refl
abstractLetterEquivP (combo (ƛ lowercase)) = refl
abstractLetterEquivP (combo (μ uppercase)) = refl
abstractLetterEquivP (combo (μ lowercase)) = refl
abstractLetterEquivP (combo (ν uppercase)) = refl
abstractLetterEquivP (combo (ν lowercase)) = refl
abstractLetterEquivP (combo (ξ uppercase)) = refl
abstractLetterEquivP (combo (ξ lowercase)) = refl
abstractLetterEquivP (combo (ο uppercase)) = refl
abstractLetterEquivP (combo (ο lowercase)) = refl
abstractLetterEquivP (combo (π uppercase)) = refl
abstractLetterEquivP (combo (π lowercase)) = refl
abstractLetterEquivP (combo (ρ uppercase)) = refl
abstractLetterEquivP (combo (ρ lowercase)) = refl
abstractLetterEquivP (combo Σ′) = refl
abstractLetterEquivP (combo (σ notFinal)) = refl
abstractLetterEquivP (combo (σ isFinal)) = refl
abstractLetterEquivP (combo (τ uppercase)) = refl
abstractLetterEquivP (combo (τ lowercase)) = refl
abstractLetterEquivP (combo (υ uppercase)) = refl
abstractLetterEquivP (combo (υ lowercase)) = refl
abstractLetterEquivP (combo (φ uppercase)) = refl
abstractLetterEquivP (combo (φ lowercase)) = refl
abstractLetterEquivP (combo (χ uppercase)) = refl
abstractLetterEquivP (combo (χ lowercase)) = refl
abstractLetterEquivP (combo (ψ uppercase)) = refl
abstractLetterEquivP (combo (ψ lowercase)) = refl
abstractLetterEquivP (combo (ω uppercase)) = refl
abstractLetterEquivP (combo (ω lowercase)) = refl

abstractLetterEquiv : Equiv ConcreteLetter Combo
abstractLetterEquiv = equiv abstractLetter abstractLetterInv abstractLetterEquivP
