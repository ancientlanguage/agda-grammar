module Language.Greek.Script where

open import Agda.Builtin.Equality
open import Agda.Primitive

data ConcreteLetter : Set where
  Α Β Γ Δ Ε Ζ Η Θ Ι Κ Λ Μ Ν Ξ Ο Π Ρ Σ Τ Υ Φ Χ Ψ Ω α β γ δ ε ζ η θ ι κ ƛ μ ν ξ ο π ρ σ ς τ υ φ χ ψ ω : ConcreteLetter

data Mark : Set where
  acute grave circumflex smooth rough diaeresis iotaSubscript : Mark

data AbstractLetter : Set where
  α β γ δ ε ζ η θ ι κ ƛ μ ν ξ ο π ρ σ τ υ φ χ ψ ω : AbstractLetter

data LetterCase : Set where
  uppercase lowercase : LetterCase

data FinalForm : AbstractLetter → LetterCase → Set where
  n/a-upper : {l : AbstractLetter} → FinalForm l uppercase
  α : FinalForm α lowercase
  β : FinalForm β lowercase
  γ : FinalForm γ lowercase
  δ : FinalForm δ lowercase
  ε : FinalForm ε lowercase
  ζ : FinalForm ζ lowercase
  η : FinalForm η lowercase
  θ : FinalForm θ lowercase
  ι : FinalForm ι lowercase
  κ : FinalForm κ lowercase
  ƛ : FinalForm ƛ lowercase
  μ : FinalForm μ lowercase
  ν : FinalForm ν lowercase
  ξ : FinalForm ξ lowercase
  ο : FinalForm ο lowercase
  π : FinalForm π lowercase
  ρ : FinalForm ρ lowercase
  τ : FinalForm τ lowercase
  υ : FinalForm υ lowercase
  φ : FinalForm φ lowercase
  χ : FinalForm χ lowercase
  ψ : FinalForm ψ lowercase
  ω : FinalForm ω lowercase
  σ ς : FinalForm σ lowercase

data AbstractCombo : Set where
  combo : (l : AbstractLetter) → (c : LetterCase) → FinalForm l c → AbstractCombo

abstractLetter : ConcreteLetter → AbstractCombo
abstractLetter Α = combo α uppercase n/a-upper
abstractLetter Β = combo β uppercase n/a-upper
abstractLetter Γ = combo γ uppercase n/a-upper
abstractLetter Δ = combo δ uppercase n/a-upper
abstractLetter Ε = combo ε uppercase n/a-upper
abstractLetter Ζ = combo ζ uppercase n/a-upper
abstractLetter Η = combo η uppercase n/a-upper
abstractLetter Θ = combo θ uppercase n/a-upper
abstractLetter Ι = combo ι uppercase n/a-upper
abstractLetter Κ = combo κ uppercase n/a-upper
abstractLetter Λ = combo ƛ uppercase n/a-upper
abstractLetter Μ = combo μ uppercase n/a-upper
abstractLetter Ν = combo ν uppercase n/a-upper
abstractLetter Ξ = combo ξ uppercase n/a-upper
abstractLetter Ο = combo ο uppercase n/a-upper
abstractLetter Π = combo π uppercase n/a-upper
abstractLetter Ρ = combo ρ uppercase n/a-upper
abstractLetter Σ = combo σ uppercase n/a-upper
abstractLetter Τ = combo τ uppercase n/a-upper
abstractLetter Υ = combo υ uppercase n/a-upper
abstractLetter Φ = combo φ uppercase n/a-upper
abstractLetter Χ = combo χ uppercase n/a-upper
abstractLetter Ψ = combo ψ uppercase n/a-upper
abstractLetter Ω = combo ω uppercase n/a-upper
abstractLetter α = combo α lowercase α
abstractLetter β = combo β lowercase β
abstractLetter γ = combo γ lowercase γ
abstractLetter δ = combo δ lowercase δ
abstractLetter ε = combo ε lowercase ε
abstractLetter ζ = combo ζ lowercase ζ
abstractLetter η = combo η lowercase η
abstractLetter θ = combo θ lowercase θ
abstractLetter ι = combo ι lowercase ι
abstractLetter κ = combo κ lowercase κ
abstractLetter ƛ = combo ƛ lowercase ƛ
abstractLetter μ = combo μ lowercase μ
abstractLetter ν = combo ν lowercase ν
abstractLetter ξ = combo ξ lowercase ξ
abstractLetter ο = combo ο lowercase ο
abstractLetter π = combo π lowercase π
abstractLetter ρ = combo ρ lowercase ρ
abstractLetter σ = combo σ lowercase σ
abstractLetter ς = combo σ lowercase ς
abstractLetter τ = combo τ lowercase τ
abstractLetter υ = combo υ lowercase υ
abstractLetter φ = combo φ lowercase φ
abstractLetter χ = combo χ lowercase χ
abstractLetter ψ = combo ψ lowercase ψ
abstractLetter ω = combo ω lowercase ω

abstractLetterInv : AbstractCombo → ConcreteLetter
abstractLetterInv (combo α uppercase n/a-upper) = Α
abstractLetterInv (combo α lowercase α) = α
abstractLetterInv (combo β uppercase n/a-upper) = Β
abstractLetterInv (combo β lowercase β) = β
abstractLetterInv (combo γ uppercase n/a-upper) = Γ
abstractLetterInv (combo γ lowercase γ) = γ
abstractLetterInv (combo δ uppercase n/a-upper) = Δ
abstractLetterInv (combo δ lowercase δ) = δ
abstractLetterInv (combo ε uppercase n/a-upper) = Ε
abstractLetterInv (combo ε lowercase ε) = ε
abstractLetterInv (combo ζ uppercase n/a-upper) = Ζ
abstractLetterInv (combo ζ lowercase ζ) = ζ
abstractLetterInv (combo η uppercase n/a-upper) = Η
abstractLetterInv (combo η lowercase η) = η
abstractLetterInv (combo θ uppercase n/a-upper) = Θ
abstractLetterInv (combo θ lowercase θ) = θ
abstractLetterInv (combo ι uppercase n/a-upper) = Ι
abstractLetterInv (combo ι lowercase ι) = ι
abstractLetterInv (combo κ uppercase n/a-upper) = Κ
abstractLetterInv (combo κ lowercase κ) = κ
abstractLetterInv (combo ƛ uppercase n/a-upper) = Λ
abstractLetterInv (combo ƛ lowercase ƛ) = ƛ
abstractLetterInv (combo μ uppercase n/a-upper) = Μ
abstractLetterInv (combo μ lowercase μ) = μ
abstractLetterInv (combo ν uppercase n/a-upper) = Ν
abstractLetterInv (combo ν lowercase ν) = ν
abstractLetterInv (combo ξ uppercase n/a-upper) = Ξ
abstractLetterInv (combo ξ lowercase ξ) = ξ
abstractLetterInv (combo ο uppercase n/a-upper) = Ο
abstractLetterInv (combo ο lowercase ο) = ο
abstractLetterInv (combo π uppercase n/a-upper) = Π
abstractLetterInv (combo π lowercase π) = π
abstractLetterInv (combo ρ uppercase n/a-upper) = Ρ
abstractLetterInv (combo ρ lowercase ρ) = ρ
abstractLetterInv (combo σ uppercase n/a-upper) = Σ
abstractLetterInv (combo σ lowercase σ) = σ
abstractLetterInv (combo σ lowercase ς) = ς
abstractLetterInv (combo τ uppercase n/a-upper) = Τ
abstractLetterInv (combo τ lowercase τ) = τ
abstractLetterInv (combo υ uppercase n/a-upper) = Υ
abstractLetterInv (combo υ lowercase υ) = υ
abstractLetterInv (combo φ uppercase n/a-upper) = Φ
abstractLetterInv (combo φ lowercase φ) = φ
abstractLetterInv (combo χ uppercase n/a-upper) = Χ
abstractLetterInv (combo χ lowercase χ) = χ
abstractLetterInv (combo ψ uppercase n/a-upper) = Ψ
abstractLetterInv (combo ψ lowercase ψ) = ψ
abstractLetterInv (combo ω uppercase n/a-upper) = Ω
abstractLetterInv (combo ω lowercase ω) = ω

concreteAbstractEquiv : (l : ConcreteLetter) → (abstractLetterInv (abstractLetter l) ≡ l)
concreteAbstractEquiv Α = refl
concreteAbstractEquiv Β = refl
concreteAbstractEquiv Γ = refl
concreteAbstractEquiv Δ = refl
concreteAbstractEquiv Ε = refl
concreteAbstractEquiv Ζ = refl
concreteAbstractEquiv Η = refl
concreteAbstractEquiv Θ = refl
concreteAbstractEquiv Ι = refl
concreteAbstractEquiv Κ = refl
concreteAbstractEquiv Λ = refl
concreteAbstractEquiv Μ = refl
concreteAbstractEquiv Ν = refl
concreteAbstractEquiv Ξ = refl
concreteAbstractEquiv Ο = refl
concreteAbstractEquiv Π = refl
concreteAbstractEquiv Ρ = refl
concreteAbstractEquiv Σ = refl
concreteAbstractEquiv Τ = refl
concreteAbstractEquiv Υ = refl
concreteAbstractEquiv Φ = refl
concreteAbstractEquiv Χ = refl
concreteAbstractEquiv Ψ = refl
concreteAbstractEquiv Ω = refl
concreteAbstractEquiv α = refl
concreteAbstractEquiv β = refl
concreteAbstractEquiv γ = refl
concreteAbstractEquiv δ = refl
concreteAbstractEquiv ε = refl
concreteAbstractEquiv ζ = refl
concreteAbstractEquiv η = refl
concreteAbstractEquiv θ = refl
concreteAbstractEquiv ι = refl
concreteAbstractEquiv κ = refl
concreteAbstractEquiv ƛ = refl
concreteAbstractEquiv μ = refl
concreteAbstractEquiv ν = refl
concreteAbstractEquiv ξ = refl
concreteAbstractEquiv ο = refl
concreteAbstractEquiv π = refl
concreteAbstractEquiv ρ = refl
concreteAbstractEquiv σ = refl
concreteAbstractEquiv ς = refl
concreteAbstractEquiv τ = refl
concreteAbstractEquiv υ = refl
concreteAbstractEquiv φ = refl
concreteAbstractEquiv χ = refl
concreteAbstractEquiv ψ = refl
concreteAbstractEquiv ω = refl
