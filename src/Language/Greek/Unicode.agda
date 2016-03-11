module Language.Greek.Unicode where

open import Agda.Builtin.Char
open import Agda.Builtin.Equality
open import Language.Greek.Concrete
open import Language.Greek.Common

concreteCombined : Char → Char PartialResultTo Combined
concreteCombined 'Α' = defined Α
concreteCombined 'Β' = defined Β
concreteCombined 'Γ' = defined Γ
concreteCombined 'Δ' = defined Δ
concreteCombined 'Ε' = defined Ε
concreteCombined 'Ζ' = defined Ζ
concreteCombined 'Η' = defined Η
concreteCombined 'Θ' = defined Θ
concreteCombined 'Ι' = defined Ι
concreteCombined 'Κ' = defined Κ
concreteCombined 'Λ' = defined Λ
concreteCombined 'Μ' = defined Μ
concreteCombined 'Ν' = defined Ν
concreteCombined 'Ξ' = defined Ξ
concreteCombined 'Ο' = defined Ο
concreteCombined 'Π' = defined Π
concreteCombined 'Ρ' = defined Ρ
concreteCombined 'Σ' = defined Σ′
concreteCombined 'Τ' = defined Τ
concreteCombined 'Υ' = defined Υ
concreteCombined 'Φ' = defined Φ
concreteCombined 'Χ' = defined Χ
concreteCombined 'Ψ' = defined Ψ
concreteCombined 'Ω' = defined Ω
concreteCombined 'α' = defined α
concreteCombined 'β' = defined β
concreteCombined 'γ' = defined γ
concreteCombined 'δ' = defined δ
concreteCombined 'ε' = defined ε
concreteCombined 'ζ' = defined ζ
concreteCombined 'η' = defined η
concreteCombined 'θ' = defined θ
concreteCombined 'ι' = defined ι
concreteCombined 'κ' = defined κ
concreteCombined 'λ' = defined ƛ
concreteCombined 'μ' = defined μ
concreteCombined 'ν' = defined ν
concreteCombined 'ξ' = defined ξ
concreteCombined 'ο' = defined ο
concreteCombined 'π' = defined π
concreteCombined 'ρ' = defined ρ
concreteCombined 'ς' = defined ς
concreteCombined 'σ' = defined σ
concreteCombined 'τ' = defined τ
concreteCombined 'υ' = defined υ
concreteCombined 'φ' = defined φ
concreteCombined 'χ' = defined χ
concreteCombined 'ψ' = defined ψ
concreteCombined 'ω' = defined ω
concreteCombined '\x0300' = defined grave -- COMBINING GRAVE ACCENT
concreteCombined '\x0301' = defined acute -- COMBINING ACUTE ACCENT
concreteCombined '\x0308' = defined diaeresis -- COMBINING DIAERESIS
concreteCombined '\x0313' = defined smooth -- COMBINING COMMA ABOVE
concreteCombined '\x0314' = defined rough -- COMBINING REVERSED COMMA ABOVE
concreteCombined '\x0342' = defined circumflex -- COMBINING GREEK PERISPOMENI
concreteCombined '\x0345' = defined iotaSubscript -- COMBINING GREEK YPOGEGRAMMENI
concreteCombined c = undefined c

concreteCombinedInv : Combined → Char
concreteCombinedInv Α = 'Α'
concreteCombinedInv Β = 'Β'
concreteCombinedInv Γ = 'Γ'
concreteCombinedInv Δ = 'Δ'
concreteCombinedInv Ε = 'Ε'
concreteCombinedInv Ζ = 'Ζ'
concreteCombinedInv Η = 'Η'
concreteCombinedInv Θ = 'Θ'
concreteCombinedInv Ι = 'Ι'
concreteCombinedInv Κ = 'Κ'
concreteCombinedInv Λ = 'Λ'
concreteCombinedInv Μ = 'Μ'
concreteCombinedInv Ν = 'Ν'
concreteCombinedInv Ξ = 'Ξ'
concreteCombinedInv Ο = 'Ο'
concreteCombinedInv Π = 'Π'
concreteCombinedInv Ρ = 'Ρ'
concreteCombinedInv Σ′ = 'Σ'
concreteCombinedInv Τ = 'Τ'
concreteCombinedInv Υ = 'Υ'
concreteCombinedInv Φ = 'Φ'
concreteCombinedInv Χ = 'Χ'
concreteCombinedInv Ψ = 'Ψ'
concreteCombinedInv Ω = 'Ω'
concreteCombinedInv α = 'α'
concreteCombinedInv β = 'β'
concreteCombinedInv γ = 'γ'
concreteCombinedInv δ = 'δ'
concreteCombinedInv ε = 'ε'
concreteCombinedInv ζ = 'ζ'
concreteCombinedInv η = 'η'
concreteCombinedInv θ = 'θ'
concreteCombinedInv ι = 'ι'
concreteCombinedInv κ = 'κ'
concreteCombinedInv ƛ = 'λ'
concreteCombinedInv μ = 'μ'
concreteCombinedInv ν = 'ν'
concreteCombinedInv ξ = 'ξ'
concreteCombinedInv ο = 'ο'
concreteCombinedInv π = 'π'
concreteCombinedInv ρ = 'ρ'
concreteCombinedInv ς = 'ς'
concreteCombinedInv σ = 'σ'
concreteCombinedInv τ = 'τ'
concreteCombinedInv υ = 'υ'
concreteCombinedInv φ = 'φ'
concreteCombinedInv χ = 'χ'
concreteCombinedInv ψ = 'ψ'
concreteCombinedInv ω = 'ω'
concreteCombinedInv grave = '\x0300' -- COMBINING GRAVE ACCENT
concreteCombinedInv acute = '\x0301' -- COMBINING ACUTE ACCENT
concreteCombinedInv diaeresis = '\x0308' -- COMBINING DIAERESIS
concreteCombinedInv smooth = '\x0313' -- COMBINING COMMA ABOVE
concreteCombinedInv rough = '\x0314' -- COMBINING REVERSED COMMA ABOVE
concreteCombinedInv circumflex = '\x0342' -- COMBINING GREEK PERISPOMENI
concreteCombinedInv iotaSubscript = '\x0345' -- COMBINING GREEK YPOGEGRAMMENI

concreteCombinedEquiv : (c : Combined) → defined c ≡ concreteCombined (concreteCombinedInv c)
concreteCombinedEquiv Α = refl
concreteCombinedEquiv Β = refl
concreteCombinedEquiv Γ = refl
concreteCombinedEquiv Δ = refl
concreteCombinedEquiv Ε = refl
concreteCombinedEquiv Ζ = refl
concreteCombinedEquiv Η = refl
concreteCombinedEquiv Θ = refl
concreteCombinedEquiv Ι = refl
concreteCombinedEquiv Κ = refl
concreteCombinedEquiv Λ = refl
concreteCombinedEquiv Μ = refl
concreteCombinedEquiv Ν = refl
concreteCombinedEquiv Ξ = refl
concreteCombinedEquiv Ο = refl
concreteCombinedEquiv Π = refl
concreteCombinedEquiv Ρ = refl
concreteCombinedEquiv Σ′ = refl
concreteCombinedEquiv Τ = refl
concreteCombinedEquiv Υ = refl
concreteCombinedEquiv Φ = refl
concreteCombinedEquiv Χ = refl
concreteCombinedEquiv Ψ = refl
concreteCombinedEquiv Ω = refl
concreteCombinedEquiv α = refl
concreteCombinedEquiv β = refl
concreteCombinedEquiv γ = refl
concreteCombinedEquiv δ = refl
concreteCombinedEquiv ε = refl
concreteCombinedEquiv ζ = refl
concreteCombinedEquiv η = refl
concreteCombinedEquiv θ = refl
concreteCombinedEquiv ι = refl
concreteCombinedEquiv κ = refl
concreteCombinedEquiv ƛ = refl
concreteCombinedEquiv μ = refl
concreteCombinedEquiv ν = refl
concreteCombinedEquiv ξ = refl
concreteCombinedEquiv ο = refl
concreteCombinedEquiv π = refl
concreteCombinedEquiv ρ = refl
concreteCombinedEquiv σ = refl
concreteCombinedEquiv ς = refl
concreteCombinedEquiv τ = refl
concreteCombinedEquiv υ = refl
concreteCombinedEquiv φ = refl
concreteCombinedEquiv χ = refl
concreteCombinedEquiv ψ = refl
concreteCombinedEquiv ω = refl
concreteCombinedEquiv acute = refl
concreteCombinedEquiv grave = refl
concreteCombinedEquiv circumflex = refl
concreteCombinedEquiv smooth = refl
concreteCombinedEquiv rough = refl
concreteCombinedEquiv diaeresis = refl
concreteCombinedEquiv iotaSubscript = refl
