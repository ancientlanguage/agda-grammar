module Language.Greek.AbstractConcrete where

open import Agda.Builtin.Equality
open import Prelude.Product
open import Prelude.Maybe
open import Language.Greek.Concrete renaming (Letter to ConcreteLetter)
open import Language.Greek.Abstract renaming (Letter to AbstractLetter)

abstractLetter
  : ConcreteLetter
  → Σ AbstractLetter λ l
    → Σ Case λ c
    → Σ (Maybe Final) λ f
    → Combo l c f
abstractLetter Α = α , uppercase , nothing , α _
abstractLetter Β = β , uppercase , nothing , β _
abstractLetter Γ = γ , uppercase , nothing , γ _
abstractLetter Δ = δ , uppercase , nothing , δ _
abstractLetter Ε = ε , uppercase , nothing , ε _
abstractLetter Ζ = ζ , uppercase , nothing , ζ _
abstractLetter Η = η , uppercase , nothing , η _
abstractLetter Θ = θ , uppercase , nothing , θ _
abstractLetter Ι = ι , uppercase , nothing , ι _
abstractLetter Κ = κ , uppercase , nothing , κ _
abstractLetter Λ = ƛ , uppercase , nothing , ƛ _
abstractLetter Μ = μ , uppercase , nothing , μ _
abstractLetter Ν = ν , uppercase , nothing , ν _
abstractLetter Ξ = ξ , uppercase , nothing , ξ _
abstractLetter Ο = ο , uppercase , nothing , ο _
abstractLetter Π = π , uppercase , nothing , π _
abstractLetter Ρ = ρ , uppercase , nothing , ρ _
abstractLetter Σ′ = σ , uppercase , nothing , Σ′
abstractLetter Τ = τ , uppercase , nothing , τ _
abstractLetter Υ = υ , uppercase , nothing , υ _
abstractLetter Φ = φ , uppercase , nothing , φ _
abstractLetter Χ = χ , uppercase , nothing , χ _
abstractLetter Ψ = ψ , uppercase , nothing , ψ _
abstractLetter Ω = ω , uppercase , nothing , ω _
abstractLetter α = α , lowercase , nothing , α _
abstractLetter β = β , lowercase , nothing , β _
abstractLetter γ = γ , lowercase , nothing , γ _
abstractLetter δ = δ , lowercase , nothing , δ _
abstractLetter ε = ε , lowercase , nothing , ε _
abstractLetter ζ = ζ , lowercase , nothing , ζ _
abstractLetter η = η , lowercase , nothing , η _
abstractLetter θ = θ , lowercase , nothing , θ _
abstractLetter ι = ι , lowercase , nothing , ι _
abstractLetter κ = κ , lowercase , nothing , κ _
abstractLetter ƛ = ƛ , lowercase , nothing , ƛ _
abstractLetter μ = μ , lowercase , nothing , μ _
abstractLetter ν = ν , lowercase , nothing , ν _
abstractLetter ξ = ξ , lowercase , nothing , ξ _
abstractLetter ο = ο , lowercase , nothing , ο _
abstractLetter π = π , lowercase , nothing , π _
abstractLetter ρ = ρ , lowercase , nothing , ρ _
abstractLetter σ = σ , lowercase , just notFinal , σ _
abstractLetter ς = σ , lowercase , just isFinal , σ _
abstractLetter τ = τ , lowercase , nothing , τ _
abstractLetter υ = υ , lowercase , nothing , υ _
abstractLetter φ = φ , lowercase , nothing , φ _
abstractLetter χ = χ , lowercase , nothing , χ _
abstractLetter ψ = ψ , lowercase , nothing , ψ _
abstractLetter ω = ω , lowercase , nothing , ω _

abstractLetterInv
  : {l : AbstractLetter}
  → {c : Case}
  → {f : Maybe Final}
  → Combo l c f
  → ConcreteLetter
abstractLetterInv (α uppercase) = Α
abstractLetterInv (α lowercase) = α
abstractLetterInv (β uppercase) = Β
abstractLetterInv (β lowercase) = β
abstractLetterInv (γ uppercase) = Γ
abstractLetterInv (γ lowercase) = γ
abstractLetterInv (δ uppercase) = Δ
abstractLetterInv (δ lowercase) = δ
abstractLetterInv (ε uppercase) = Ε
abstractLetterInv (ε lowercase) = ε
abstractLetterInv (ζ uppercase) = Ζ
abstractLetterInv (ζ lowercase) = ζ
abstractLetterInv (η uppercase) = Η
abstractLetterInv (η lowercase) = η
abstractLetterInv (θ uppercase) = Θ
abstractLetterInv (θ lowercase) = θ
abstractLetterInv (ι uppercase) = Ι
abstractLetterInv (ι lowercase) = ι
abstractLetterInv (κ uppercase) = Κ
abstractLetterInv (κ lowercase) = κ
abstractLetterInv (ƛ uppercase) = Λ
abstractLetterInv (ƛ lowercase) = ƛ
abstractLetterInv (μ uppercase) = Μ
abstractLetterInv (μ lowercase) = μ
abstractLetterInv (ν uppercase) = Ν
abstractLetterInv (ν lowercase) = ν
abstractLetterInv (ξ uppercase) = Ξ
abstractLetterInv (ξ lowercase) = ξ
abstractLetterInv (ο uppercase) = Ο
abstractLetterInv (ο lowercase) = ο
abstractLetterInv (π uppercase) = Π
abstractLetterInv (π lowercase) = π
abstractLetterInv (ρ uppercase) = Ρ
abstractLetterInv (ρ lowercase) = ρ
abstractLetterInv Σ′ = Σ′
abstractLetterInv (σ notFinal) = σ
abstractLetterInv (σ isFinal) = ς
abstractLetterInv (τ uppercase) = Τ
abstractLetterInv (τ lowercase) = τ
abstractLetterInv (υ uppercase) = Υ
abstractLetterInv (υ lowercase) = υ
abstractLetterInv (φ uppercase) = Φ
abstractLetterInv (φ lowercase) = φ
abstractLetterInv (χ uppercase) = Χ
abstractLetterInv (χ lowercase) = χ
abstractLetterInv (ψ uppercase) = Ψ
abstractLetterInv (ψ lowercase) = ψ
abstractLetterInv (ω uppercase) = Ω
abstractLetterInv (ω lowercase) = ω

abstractLetterEquiv
  : (a : Σ AbstractLetter λ l
    → Σ Case λ c
    → Σ (Maybe Final) λ f
    → Combo l c f)
  → a ≡ abstractLetter (abstractLetterInv (snd (snd (snd a))))
abstractLetterEquiv (α , uppercase , nothing , α .uppercase) = refl
abstractLetterEquiv (α , lowercase , nothing , α .lowercase) = refl
abstractLetterEquiv (β , uppercase , nothing , β .uppercase) = refl
abstractLetterEquiv (β , lowercase , nothing , β .lowercase) = refl
abstractLetterEquiv (γ , uppercase , nothing , γ .uppercase) = refl
abstractLetterEquiv (γ , lowercase , nothing , γ .lowercase) = refl
abstractLetterEquiv (δ , uppercase , nothing , δ .uppercase) = refl
abstractLetterEquiv (δ , lowercase , nothing , δ .lowercase) = refl
abstractLetterEquiv (ε , uppercase , nothing , ε .uppercase) = refl
abstractLetterEquiv (ε , lowercase , nothing , ε .lowercase) = refl
abstractLetterEquiv (ζ , uppercase , nothing , ζ .uppercase) = refl
abstractLetterEquiv (ζ , lowercase , nothing , ζ .lowercase) = refl
abstractLetterEquiv (η , uppercase , nothing , η .uppercase) = refl
abstractLetterEquiv (η , lowercase , nothing , η .lowercase) = refl
abstractLetterEquiv (θ , uppercase , nothing , θ .uppercase) = refl
abstractLetterEquiv (θ , lowercase , nothing , θ .lowercase) = refl
abstractLetterEquiv (ι , uppercase , nothing , ι .uppercase) = refl
abstractLetterEquiv (ι , lowercase , nothing , ι .lowercase) = refl
abstractLetterEquiv (κ , uppercase , nothing , κ .uppercase) = refl
abstractLetterEquiv (κ , lowercase , nothing , κ .lowercase) = refl
abstractLetterEquiv (ƛ , uppercase , nothing , ƛ .uppercase) = refl
abstractLetterEquiv (ƛ , lowercase , nothing , ƛ .lowercase) = refl
abstractLetterEquiv (μ , uppercase , nothing , μ .uppercase) = refl
abstractLetterEquiv (μ , lowercase , nothing , μ .lowercase) = refl
abstractLetterEquiv (ν , uppercase , nothing , ν .uppercase) = refl
abstractLetterEquiv (ν , lowercase , nothing , ν .lowercase) = refl
abstractLetterEquiv (ξ , uppercase , nothing , ξ .uppercase) = refl
abstractLetterEquiv (ξ , lowercase , nothing , ξ .lowercase) = refl
abstractLetterEquiv (ο , uppercase , nothing , ο .uppercase) = refl
abstractLetterEquiv (ο , lowercase , nothing , ο .lowercase) = refl
abstractLetterEquiv (π , uppercase , nothing , π .uppercase) = refl
abstractLetterEquiv (π , lowercase , nothing , π .lowercase) = refl
abstractLetterEquiv (ρ , uppercase , nothing , ρ .uppercase) = refl
abstractLetterEquiv (ρ , lowercase , nothing , ρ .lowercase) = refl
abstractLetterEquiv (σ , uppercase , nothing , Σ′) = refl
abstractLetterEquiv (σ , lowercase , just isFinal , σ .isFinal) = refl
abstractLetterEquiv (σ , lowercase , just notFinal , σ .notFinal) = refl
abstractLetterEquiv (τ , uppercase , nothing , τ .uppercase) = refl
abstractLetterEquiv (τ , lowercase , nothing , τ .lowercase) = refl
abstractLetterEquiv (υ , uppercase , nothing , υ .uppercase) = refl
abstractLetterEquiv (υ , lowercase , nothing , υ .lowercase) = refl
abstractLetterEquiv (φ , uppercase , nothing , φ .uppercase) = refl
abstractLetterEquiv (φ , lowercase , nothing , φ .lowercase) = refl
abstractLetterEquiv (χ , uppercase , nothing , χ .uppercase) = refl
abstractLetterEquiv (χ , lowercase , nothing , χ .lowercase) = refl
abstractLetterEquiv (ψ , uppercase , nothing , ψ .uppercase) = refl
abstractLetterEquiv (ψ , lowercase , nothing , ψ .lowercase) = refl
abstractLetterEquiv (ω , uppercase , nothing , ω .uppercase) = refl
abstractLetterEquiv (ω , lowercase , nothing , ω .lowercase) = refl

abstractLetterEquiv'
  : (c : ConcreteLetter)
  → c ≡ abstractLetterInv (snd (snd (snd (abstractLetter c))))
abstractLetterEquiv' Α = refl
abstractLetterEquiv' Β = refl
abstractLetterEquiv' Γ = refl
abstractLetterEquiv' Δ = refl
abstractLetterEquiv' Ε = refl
abstractLetterEquiv' Ζ = refl
abstractLetterEquiv' Η = refl
abstractLetterEquiv' Θ = refl
abstractLetterEquiv' Ι = refl
abstractLetterEquiv' Κ = refl
abstractLetterEquiv' Λ = refl
abstractLetterEquiv' Μ = refl
abstractLetterEquiv' Ν = refl
abstractLetterEquiv' Ξ = refl
abstractLetterEquiv' Ο = refl
abstractLetterEquiv' Π = refl
abstractLetterEquiv' Ρ = refl
abstractLetterEquiv' Σ′ = refl
abstractLetterEquiv' Τ = refl
abstractLetterEquiv' Υ = refl
abstractLetterEquiv' Φ = refl
abstractLetterEquiv' Χ = refl
abstractLetterEquiv' Ψ = refl
abstractLetterEquiv' Ω = refl
abstractLetterEquiv' α = refl
abstractLetterEquiv' β = refl
abstractLetterEquiv' γ = refl
abstractLetterEquiv' δ = refl
abstractLetterEquiv' ε = refl
abstractLetterEquiv' ζ = refl
abstractLetterEquiv' η = refl
abstractLetterEquiv' θ = refl
abstractLetterEquiv' ι = refl
abstractLetterEquiv' κ = refl
abstractLetterEquiv' ƛ = refl
abstractLetterEquiv' μ = refl
abstractLetterEquiv' ν = refl
abstractLetterEquiv' ξ = refl
abstractLetterEquiv' ο = refl
abstractLetterEquiv' π = refl
abstractLetterEquiv' ρ = refl
abstractLetterEquiv' σ = refl
abstractLetterEquiv' ς = refl
abstractLetterEquiv' τ = refl
abstractLetterEquiv' υ = refl
abstractLetterEquiv' φ = refl
abstractLetterEquiv' χ = refl
abstractLetterEquiv' ψ = refl
abstractLetterEquiv' ω = refl
