module Language.Greek.Unicode where

open import Agda.Builtin.Char
open import Agda.Builtin.Equality
open import Agda.Builtin.Unit
open import Language.Greek.Concrete
open import Prelude.Empty
open import Prelude.Maybe
open import Prelude.Bool

data GreekChar : Set where
  valid : Combined -> GreekChar
  invalid : Char -> GreekChar

validateGreekChar : GreekChar → Set
validateGreekChar (valid x) = ⊤
validateGreekChar (invalid x) = ⊥

extractCombined : (x : GreekChar) {_ : validateGreekChar x} → Combined
extractCombined (valid x) = x
extractCombined (invalid x) {}

concreteCombined : Char → GreekChar
concreteCombined 'Α' = valid Α
concreteCombined 'Β' = valid Β
concreteCombined 'Γ' = valid Γ
concreteCombined 'Δ' = valid Δ
concreteCombined 'Ε' = valid Ε
concreteCombined 'Ζ' = valid Ζ
concreteCombined 'Η' = valid Η
concreteCombined 'Θ' = valid Θ
concreteCombined 'Ι' = valid Ι
concreteCombined 'Κ' = valid Κ
concreteCombined 'Λ' = valid Λ
concreteCombined 'Μ' = valid Μ
concreteCombined 'Ν' = valid Ν
concreteCombined 'Ξ' = valid Ξ
concreteCombined 'Ο' = valid Ο
concreteCombined 'Π' = valid Π
concreteCombined 'Ρ' = valid Ρ
concreteCombined 'Σ' = valid Σ′
concreteCombined 'Τ' = valid Τ
concreteCombined 'Υ' = valid Υ
concreteCombined 'Φ' = valid Φ
concreteCombined 'Χ' = valid Χ
concreteCombined 'Ψ' = valid Ψ
concreteCombined 'Ω' = valid Ω
concreteCombined 'α' = valid α
concreteCombined 'β' = valid β
concreteCombined 'γ' = valid γ
concreteCombined 'δ' = valid δ
concreteCombined 'ε' = valid ε
concreteCombined 'ζ' = valid ζ
concreteCombined 'η' = valid η
concreteCombined 'θ' = valid θ
concreteCombined 'ι' = valid ι
concreteCombined 'κ' = valid κ
concreteCombined 'λ' = valid ƛ
concreteCombined 'μ' = valid μ
concreteCombined 'ν' = valid ν
concreteCombined 'ξ' = valid ξ
concreteCombined 'ο' = valid ο
concreteCombined 'π' = valid π
concreteCombined 'ρ' = valid ρ
concreteCombined 'ς' = valid ς
concreteCombined 'σ' = valid σ
concreteCombined 'τ' = valid τ
concreteCombined 'υ' = valid υ
concreteCombined 'φ' = valid φ
concreteCombined 'χ' = valid χ
concreteCombined 'ψ' = valid ψ
concreteCombined 'ω' = valid ω
concreteCombined '\x0300' = valid grave -- COMBINING GRAVE ACCENT
concreteCombined '\x0301' = valid acute -- COMBINING ACUTE ACCENT
concreteCombined '\x0308' = valid diaeresis -- COMBINING DIAERESIS
concreteCombined '\x0313' = valid smooth -- COMBINING COMMA ABOVE
concreteCombined '\x0314' = valid rough -- COMBINING REVERSED COMMA ABOVE
concreteCombined '\x0342' = valid circumflex -- COMBINING GREEK PERISPOMENI
concreteCombined '\x0345' = valid iotaSubscript -- COMBINING GREEK YPOGEGRAMMENI
concreteCombined c = invalid c

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

concreteCombinedEquiv : (c : Combined) → valid c ≡ concreteCombined (concreteCombinedInv c)
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
