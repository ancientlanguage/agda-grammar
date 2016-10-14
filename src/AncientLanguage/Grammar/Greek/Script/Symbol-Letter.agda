module AncientLanguage.Grammar.Greek.Script.Symbol-Letter where

open import AncientLanguage.Grammar.Greek.Script.Letter
open import AncientLanguage.Grammar.Greek.Script.Symbol

to : Symbol → LetterCaseFinalRecord
to Α = letter-case-final-record (α upper)
to Β = letter-case-final-record (β upper)
to Γ = letter-case-final-record (γ upper)
to Δ = letter-case-final-record (δ upper)
to Ε = letter-case-final-record (ε upper)
to Ζ = letter-case-final-record (ζ upper)
to Η = letter-case-final-record (η upper)
to Θ = letter-case-final-record (θ upper)
to Ι = letter-case-final-record (ι upper)
to Κ = letter-case-final-record (κ upper)
to Λ = letter-case-final-record (ƛ upper)
to Μ = letter-case-final-record (μ upper)
to Ν = letter-case-final-record (ν upper)
to Ξ = letter-case-final-record (ξ upper)
to Ο = letter-case-final-record (ο upper)
to Π = letter-case-final-record (π upper)
to Ρ = letter-case-final-record (ρ upper)
to Σ = letter-case-final-record Σ
to Τ = letter-case-final-record (τ upper)
to Υ = letter-case-final-record (υ upper)
to Φ = letter-case-final-record (φ upper)
to Χ = letter-case-final-record (χ upper)
to Ψ = letter-case-final-record (ψ upper)
to Ω = letter-case-final-record (ω upper)
to α = letter-case-final-record (α lower)
to β = letter-case-final-record (β lower)
to γ = letter-case-final-record (γ lower)
to δ = letter-case-final-record (δ lower)
to ε = letter-case-final-record (ε lower)
to ζ = letter-case-final-record (ζ lower)
to η = letter-case-final-record (η lower)
to θ = letter-case-final-record (θ lower)
to ι = letter-case-final-record (ι lower)
to κ = letter-case-final-record (κ lower)
to ƛ = letter-case-final-record (ƛ lower)
to μ = letter-case-final-record (μ lower)
to ν = letter-case-final-record (ν lower)
to ξ = letter-case-final-record (ξ lower)
to ο = letter-case-final-record (ο lower)
to π = letter-case-final-record (π lower)
to ρ = letter-case-final-record (ρ lower)
to σ = letter-case-final-record σ
to ς = letter-case-final-record ς
to τ = letter-case-final-record (τ lower)
to υ = letter-case-final-record (υ lower)
to φ = letter-case-final-record (φ lower)
to χ = letter-case-final-record (χ lower)
to ψ = letter-case-final-record (ψ lower)
to ω = letter-case-final-record (ω lower)

from : LetterCaseFinalRecord → Symbol
from (letter-case-final-record (α upper)) = Α
from (letter-case-final-record (α lower)) = α
from (letter-case-final-record (β upper)) = Β
from (letter-case-final-record (β lower)) = β
from (letter-case-final-record (γ upper)) = Γ
from (letter-case-final-record (γ lower)) = γ
from (letter-case-final-record (δ upper)) = Δ
from (letter-case-final-record (δ lower)) = δ
from (letter-case-final-record (ε upper)) = Ε
from (letter-case-final-record (ε lower)) = ε
from (letter-case-final-record (ζ upper)) = Ζ
from (letter-case-final-record (ζ lower)) = ζ
from (letter-case-final-record (η upper)) = Η
from (letter-case-final-record (η lower)) = η
from (letter-case-final-record (θ upper)) = Θ
from (letter-case-final-record (θ lower)) = θ
from (letter-case-final-record (ι upper)) = Ι
from (letter-case-final-record (ι lower)) = ι
from (letter-case-final-record (κ upper)) = Κ
from (letter-case-final-record (κ lower)) = κ
from (letter-case-final-record (ƛ upper)) = Λ
from (letter-case-final-record (ƛ lower)) = ƛ
from (letter-case-final-record (μ upper)) = Μ
from (letter-case-final-record (μ lower)) = μ
from (letter-case-final-record (ν upper)) = Ν
from (letter-case-final-record (ν lower)) = ν
from (letter-case-final-record (ξ upper)) = Ξ
from (letter-case-final-record (ξ lower)) = ξ
from (letter-case-final-record (ο upper)) = Ο
from (letter-case-final-record (ο lower)) = ο
from (letter-case-final-record (π upper)) = Π
from (letter-case-final-record (π lower)) = π
from (letter-case-final-record (ρ upper)) = Ρ
from (letter-case-final-record (ρ lower)) = ρ
from (letter-case-final-record Σ) = Σ
from (letter-case-final-record σ) = σ
from (letter-case-final-record ς) = ς
from (letter-case-final-record (τ upper)) = Τ
from (letter-case-final-record (τ lower)) = τ
from (letter-case-final-record (υ upper)) = Υ
from (letter-case-final-record (υ lower)) = υ
from (letter-case-final-record (φ upper)) = Φ
from (letter-case-final-record (φ lower)) = φ
from (letter-case-final-record (χ upper)) = Χ
from (letter-case-final-record (χ lower)) = χ
from (letter-case-final-record (ψ upper)) = Ψ
from (letter-case-final-record (ψ lower)) = ψ
from (letter-case-final-record (ω upper)) = Ω
from (letter-case-final-record (ω lower)) = ω

module Test where
  open import Agda.Builtin.String
  open import AncientLanguage.Abstraction
  open import AncientLanguage.Grammar.Greek.Script.Mark
  import AncientLanguage.Grammar.Greek.Script.Unicode-Symbol as Unicode

  test : Fwd (Symbol + Mark)
  test = Sum.asInr (Unicode.stringToSymbol "ΑΒΓΔΕΖΗΘΙΚΛΜΝΞΟΠΡΣΤΥΦΧΨΩαβγδεζηθικλμνξοπρσςτυφχψω")

  around : (TraverseId.fwd ∘ TraverseId.inl) from ((TraverseId.fwd ∘ TraverseId.inl) to test) ≡ test
  around = refl
