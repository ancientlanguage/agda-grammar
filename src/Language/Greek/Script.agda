module Language.Greek.Script where

open import Agda.Builtin.Equality
open import Agda.Primitive
open import Prelude.Function
open import Prelude.Product
open import Prelude.Maybe

data ConcreteLetter : Set where
  Α Β Γ Δ Ε Ζ Η Θ Ι Κ Λ Μ Ν Ξ Ο Π Ρ Σ′ Τ Υ Φ Χ Ψ Ω α β γ δ ε ζ η θ ι κ ƛ μ ν ξ ο π ρ σ ς τ υ φ χ ψ ω : ConcreteLetter

data Mark : Set where
  acute grave circumflex smooth rough diaeresis iotaSubscript : Mark

data AbstractLetter : Set where
  α β γ δ ε ζ η θ ι κ ƛ μ ν ξ ο π ρ σ τ υ φ χ ψ ω : AbstractLetter

data LetterCase : Set where
  uppercase lowercase : LetterCase

data Final : Set where
  isFinal notFinal : Final

data AbstractCombo : AbstractLetter → LetterCase → Maybe Final → Set where
  α : (c : LetterCase) → AbstractCombo α c nothing
  β : (c : LetterCase) → AbstractCombo β c nothing
  γ : (c : LetterCase) → AbstractCombo γ c nothing
  δ : (c : LetterCase) → AbstractCombo δ c nothing
  ε : (c : LetterCase) → AbstractCombo ε c nothing
  ζ : (c : LetterCase) → AbstractCombo ζ c nothing
  η : (c : LetterCase) → AbstractCombo η c nothing
  θ : (c : LetterCase) → AbstractCombo θ c nothing
  ι : (c : LetterCase) → AbstractCombo ι c nothing
  κ : (c : LetterCase) → AbstractCombo κ c nothing
  ƛ : (c : LetterCase) → AbstractCombo ƛ c nothing
  μ : (c : LetterCase) → AbstractCombo μ c nothing
  ν : (c : LetterCase) → AbstractCombo ν c nothing
  ξ : (c : LetterCase) → AbstractCombo ξ c nothing
  ο : (c : LetterCase) → AbstractCombo ο c nothing
  π : (c : LetterCase) → AbstractCombo π c nothing
  ρ : (c : LetterCase) → AbstractCombo ρ c nothing
  Σ′ : AbstractCombo σ uppercase nothing
  σ : (f : Final) -> AbstractCombo σ lowercase (just f)
  τ : (c : LetterCase) → AbstractCombo τ c nothing
  υ : (c : LetterCase) → AbstractCombo υ c nothing
  φ : (c : LetterCase) → AbstractCombo φ c nothing
  χ : (c : LetterCase) → AbstractCombo χ c nothing
  ψ : (c : LetterCase) → AbstractCombo ψ c nothing
  ω : (c : LetterCase) → AbstractCombo ω c nothing

abstractLetter
  : ConcreteLetter
  → Σ AbstractLetter λ l
    → Σ LetterCase λ c
    → Σ (Maybe Final) λ f
    → AbstractCombo l c f
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
  → {c : LetterCase}
  → {f : Maybe Final}
  → AbstractCombo l c f
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

{-
abstractLetterEquiv
  : {l : AbstractLetter}
  → {c : LetterCase}
  → {f : Maybe Final}
  → (a : AbstractCombo l c f)
  → a ≡ snd (snd (snd (abstractLetter (abstractLetterInv a))))
abstractLetterEquiv = {!!}
-}

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
