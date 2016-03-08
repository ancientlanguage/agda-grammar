module Language.Greek.Script where

open import Agda.Builtin.Equality
open import Agda.Primitive
open import Prelude.Product renaming (Σ to Sg)
open import Prelude.Maybe

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


data Final : Set where
  n/a isFinal notFinal : Final

abstractLetterF : ConcreteLetter → AbstractLetter × LetterCase × Final
abstractLetterF Α = α , uppercase , n/a
abstractLetterF Β = β , uppercase , n/a
abstractLetterF Γ = γ , uppercase , n/a
abstractLetterF Δ = δ , uppercase , n/a
abstractLetterF Ε = ε , uppercase , n/a
abstractLetterF Ζ = ζ , uppercase , n/a
abstractLetterF Η = η , uppercase , n/a
abstractLetterF Θ = θ , uppercase , n/a
abstractLetterF Ι = ι , uppercase , n/a
abstractLetterF Κ = κ , uppercase , n/a
abstractLetterF Λ = ƛ , uppercase , n/a
abstractLetterF Μ = μ , uppercase , n/a
abstractLetterF Ν = ν , uppercase , n/a
abstractLetterF Ξ = ξ , uppercase , n/a
abstractLetterF Ο = ο , uppercase , n/a
abstractLetterF Π = π , uppercase , n/a
abstractLetterF Ρ = ρ , uppercase , n/a
abstractLetterF Σ = σ , uppercase , n/a
abstractLetterF Τ = τ , uppercase , n/a
abstractLetterF Υ = υ , uppercase , n/a
abstractLetterF Φ = φ , uppercase , n/a
abstractLetterF Χ = χ , uppercase , n/a
abstractLetterF Ψ = ψ , uppercase , n/a
abstractLetterF Ω = ω , uppercase , n/a
abstractLetterF α = α , lowercase , n/a
abstractLetterF β = β , lowercase , n/a
abstractLetterF γ = γ , lowercase , n/a
abstractLetterF δ = δ , lowercase , n/a
abstractLetterF ε = ε , lowercase , n/a
abstractLetterF ζ = ζ , lowercase , n/a
abstractLetterF η = η , lowercase , n/a
abstractLetterF θ = θ , lowercase , n/a
abstractLetterF ι = ι , lowercase , n/a
abstractLetterF κ = κ , lowercase , n/a
abstractLetterF ƛ = ƛ , lowercase , n/a
abstractLetterF μ = μ , lowercase , n/a
abstractLetterF ν = ν , lowercase , n/a
abstractLetterF ξ = ξ , lowercase , n/a
abstractLetterF ο = ο , lowercase , n/a
abstractLetterF π = π , lowercase , n/a
abstractLetterF ρ = ρ , lowercase , n/a
abstractLetterF σ = σ , lowercase , notFinal
abstractLetterF ς = σ , lowercase , isFinal
abstractLetterF τ = τ , lowercase , n/a
abstractLetterF υ = υ , lowercase , n/a
abstractLetterF φ = φ , lowercase , n/a
abstractLetterF χ = χ , lowercase , n/a
abstractLetterF ψ = ψ , lowercase , n/a
abstractLetterF ω = ω , lowercase , n/a

abstractLetterFInv : AbstractLetter × LetterCase × Final → Maybe ConcreteLetter
abstractLetterFInv (α , uppercase , n/a) = just Α
abstractLetterFInv (α , lowercase , n/a) = just α
abstractLetterFInv (β , uppercase , n/a) = just Β
abstractLetterFInv (β , lowercase , n/a) = just β
abstractLetterFInv (γ , uppercase , n/a) = just Γ
abstractLetterFInv (γ , lowercase , n/a) = just γ
abstractLetterFInv (δ , uppercase , n/a) = just Δ
abstractLetterFInv (δ , lowercase , n/a) = just δ
abstractLetterFInv (ε , uppercase , n/a) = just Ε
abstractLetterFInv (ε , lowercase , n/a) = just ε
abstractLetterFInv (ζ , uppercase , n/a) = just Ζ
abstractLetterFInv (ζ , lowercase , n/a) = just ζ
abstractLetterFInv (η , uppercase , n/a) = just Η
abstractLetterFInv (η , lowercase , n/a) = just η
abstractLetterFInv (θ , uppercase , n/a) = just Θ
abstractLetterFInv (θ , lowercase , n/a) = just θ
abstractLetterFInv (ι , uppercase , n/a) = just Ι
abstractLetterFInv (ι , lowercase , n/a) = just ι
abstractLetterFInv (κ , uppercase , n/a) = just Κ
abstractLetterFInv (κ , lowercase , n/a) = just κ
abstractLetterFInv (ƛ , uppercase , n/a) = just Λ
abstractLetterFInv (ƛ , lowercase , n/a) = just ƛ
abstractLetterFInv (μ , uppercase , n/a) = just Μ
abstractLetterFInv (μ , lowercase , n/a) = just μ
abstractLetterFInv (ν , uppercase , n/a) = just Ν
abstractLetterFInv (ν , lowercase , n/a) = just ν
abstractLetterFInv (ξ , uppercase , n/a) = just Ξ
abstractLetterFInv (ξ , lowercase , n/a) = just ξ
abstractLetterFInv (ο , uppercase , n/a) = just Ο
abstractLetterFInv (ο , lowercase , n/a) = just ο
abstractLetterFInv (π , uppercase , n/a) = just Π
abstractLetterFInv (π , lowercase , n/a) = just π
abstractLetterFInv (ρ , uppercase , n/a) = just Ρ
abstractLetterFInv (ρ , lowercase , n/a) = just ρ
abstractLetterFInv (σ , uppercase , n/a) = just Σ
abstractLetterFInv (σ , lowercase , isFinal) = just ς
abstractLetterFInv (σ , lowercase , notFinal) = just σ
abstractLetterFInv (τ , uppercase , n/a) = just Τ
abstractLetterFInv (τ , lowercase , n/a) = just τ
abstractLetterFInv (υ , uppercase , n/a) = just Υ
abstractLetterFInv (υ , lowercase , n/a) = just υ
abstractLetterFInv (φ , uppercase , n/a) = just Φ
abstractLetterFInv (φ , lowercase , n/a) = just φ
abstractLetterFInv (χ , uppercase , n/a) = just Χ
abstractLetterFInv (χ , lowercase , n/a) = just χ
abstractLetterFInv (ψ , uppercase , n/a) = just Ψ
abstractLetterFInv (ψ , lowercase , n/a) = just ψ
abstractLetterFInv (ω , uppercase , n/a) = just Ω
abstractLetterFInv (ω , lowercase , n/a) = just ω
abstractLetterFInv _ = nothing

concreteAbstractFEquiv : (l : ConcreteLetter) → (abstractLetterFInv (abstractLetterF l) ≡ just l)
concreteAbstractFEquiv Α = refl
concreteAbstractFEquiv Β = refl
concreteAbstractFEquiv Γ = refl
concreteAbstractFEquiv Δ = refl
concreteAbstractFEquiv Ε = refl
concreteAbstractFEquiv Ζ = refl
concreteAbstractFEquiv Η = refl
concreteAbstractFEquiv Θ = refl
concreteAbstractFEquiv Ι = refl
concreteAbstractFEquiv Κ = refl
concreteAbstractFEquiv Λ = refl
concreteAbstractFEquiv Μ = refl
concreteAbstractFEquiv Ν = refl
concreteAbstractFEquiv Ξ = refl
concreteAbstractFEquiv Ο = refl
concreteAbstractFEquiv Π = refl
concreteAbstractFEquiv Ρ = refl
concreteAbstractFEquiv Σ = refl
concreteAbstractFEquiv Τ = refl
concreteAbstractFEquiv Υ = refl
concreteAbstractFEquiv Φ = refl
concreteAbstractFEquiv Χ = refl
concreteAbstractFEquiv Ψ = refl
concreteAbstractFEquiv Ω = refl
concreteAbstractFEquiv α = refl
concreteAbstractFEquiv β = refl
concreteAbstractFEquiv γ = refl
concreteAbstractFEquiv δ = refl
concreteAbstractFEquiv ε = refl
concreteAbstractFEquiv ζ = refl
concreteAbstractFEquiv η = refl
concreteAbstractFEquiv θ = refl
concreteAbstractFEquiv ι = refl
concreteAbstractFEquiv κ = refl
concreteAbstractFEquiv ƛ = refl
concreteAbstractFEquiv μ = refl
concreteAbstractFEquiv ν = refl
concreteAbstractFEquiv ξ = refl
concreteAbstractFEquiv ο = refl
concreteAbstractFEquiv π = refl
concreteAbstractFEquiv ρ = refl
concreteAbstractFEquiv σ = refl
concreteAbstractFEquiv ς = refl
concreteAbstractFEquiv τ = refl
concreteAbstractFEquiv υ = refl
concreteAbstractFEquiv φ = refl
concreteAbstractFEquiv χ = refl
concreteAbstractFEquiv ψ = refl
concreteAbstractFEquiv ω = refl
