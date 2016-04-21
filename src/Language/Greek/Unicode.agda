module Language.Greek.Unicode where

open import Agda.Builtin.Char
open import Agda.Builtin.Equality
open import Language.Greek.Script
open import Prelude.Monoidal.Coproduct
open import Common.RoundTrip.Partial.Result
open import Common.RoundTrip.Partial.Definition

open ⊕
  using (inl)
  using (inr)

data NonGreekChar : Set where
  nonGreekChar : Char → NonGreekChar

fromChar : Char → (Symbol ⊕ Mark) ⁇ NonGreekChar
fromChar 'Α' = defined (inl Α)
fromChar 'Β' = defined (inl Β)
fromChar 'Γ' = defined (inl Γ)
fromChar 'Δ' = defined (inl Δ)
fromChar 'Ε' = defined (inl Ε)
fromChar 'Ζ' = defined (inl Ζ)
fromChar 'Η' = defined (inl Η)
fromChar 'Θ' = defined (inl Θ)
fromChar 'Ι' = defined (inl Ι)
fromChar 'Κ' = defined (inl Κ)
fromChar 'Λ' = defined (inl Λ)
fromChar 'Μ' = defined (inl Μ)
fromChar 'Ν' = defined (inl Ν)
fromChar 'Ξ' = defined (inl Ξ)
fromChar 'Ο' = defined (inl Ο)
fromChar 'Π' = defined (inl Π)
fromChar 'Ρ' = defined (inl Ρ)
fromChar 'Σ' = defined (inl Σ′)
fromChar 'Τ' = defined (inl Τ)
fromChar 'Υ' = defined (inl Υ)
fromChar 'Φ' = defined (inl Φ)
fromChar 'Χ' = defined (inl Χ)
fromChar 'Ψ' = defined (inl Ψ)
fromChar 'Ω' = defined (inl Ω)
fromChar 'α' = defined (inl α)
fromChar 'β' = defined (inl β)
fromChar 'γ' = defined (inl γ)
fromChar 'δ' = defined (inl δ)
fromChar 'ε' = defined (inl ε)
fromChar 'ζ' = defined (inl ζ)
fromChar 'η' = defined (inl η)
fromChar 'θ' = defined (inl θ)
fromChar 'ι' = defined (inl ι)
fromChar 'κ' = defined (inl κ)
fromChar 'λ' = defined (inl ƛ)
fromChar 'μ' = defined (inl μ)
fromChar 'ν' = defined (inl ν)
fromChar 'ξ' = defined (inl ξ)
fromChar 'ο' = defined (inl ο)
fromChar 'π' = defined (inl π)
fromChar 'ρ' = defined (inl ρ)
fromChar 'ς' = defined (inl ς)
fromChar 'σ' = defined (inl σ)
fromChar 'τ' = defined (inl τ)
fromChar 'υ' = defined (inl υ)
fromChar 'φ' = defined (inl φ)
fromChar 'χ' = defined (inl χ)
fromChar 'ψ' = defined (inl ψ)
fromChar 'ω' = defined (inl ω)
fromChar '\x0300' = defined (inr grave) -- COMBINING GRAVE ACCENT
fromChar '\x0301' = defined (inr acute) -- COMBINING ACUTE ACCENT
fromChar '\x0308' = defined (inr diaeresis) -- COMBINING DIAERESIS
fromChar '\x0313' = defined (inr smooth) -- COMBINING COMMA ABOVE
fromChar '\x0314' = defined (inr rough) -- COMBINING REVERSED COMMA ABOVE
fromChar '\x0342' = defined (inr circumflex) -- COMBINING GREEK PERISPOMENI
fromChar '\x0345' = defined (inr iotaSubscript) -- COMBINING GREEK YPOGEGRAMMENI
fromChar c = undefined (nonGreekChar c)

toChar : Symbol ⊕ Mark → Char
toChar (inl Α) = 'Α'
toChar (inl Β) = 'Β'
toChar (inl Γ) = 'Γ'
toChar (inl Δ) = 'Δ'
toChar (inl Ε) = 'Ε'
toChar (inl Ζ) = 'Ζ'
toChar (inl Η) = 'Η'
toChar (inl Θ) = 'Θ'
toChar (inl Ι) = 'Ι'
toChar (inl Κ) = 'Κ'
toChar (inl Λ) = 'Λ'
toChar (inl Μ) = 'Μ'
toChar (inl Ν) = 'Ν'
toChar (inl Ξ) = 'Ξ'
toChar (inl Ο) = 'Ο'
toChar (inl Π) = 'Π'
toChar (inl Ρ) = 'Ρ'
toChar (inl Σ′) = 'Σ'
toChar (inl Τ) = 'Τ'
toChar (inl Υ) = 'Υ'
toChar (inl Φ) = 'Φ'
toChar (inl Χ) = 'Χ'
toChar (inl Ψ) = 'Ψ'
toChar (inl Ω) = 'Ω'
toChar (inl α) = 'α'
toChar (inl β) = 'β'
toChar (inl γ) = 'γ'
toChar (inl δ) = 'δ'
toChar (inl ε) = 'ε'
toChar (inl ζ) = 'ζ'
toChar (inl η) = 'η'
toChar (inl θ) = 'θ'
toChar (inl ι) = 'ι'
toChar (inl κ) = 'κ'
toChar (inl ƛ) = 'λ'
toChar (inl μ) = 'μ'
toChar (inl ν) = 'ν'
toChar (inl ξ) = 'ξ'
toChar (inl ο) = 'ο'
toChar (inl π) = 'π'
toChar (inl ρ) = 'ρ'
toChar (inl ς) = 'ς'
toChar (inl σ) = 'σ'
toChar (inl τ) = 'τ'
toChar (inl υ) = 'υ'
toChar (inl φ) = 'φ'
toChar (inl χ) = 'χ'
toChar (inl ψ) = 'ψ'
toChar (inl ω) = 'ω'
toChar (inr grave) = '\x0300' -- COMBINING GRAVE ACCENT
toChar (inr acute) = '\x0301' -- COMBINING ACUTE ACCENT
toChar (inr diaeresis) = '\x0308' -- COMBINING DIAERESIS
toChar (inr smooth) = '\x0313' -- COMBINING COMMA ABOVE
toChar (inr rough) = '\x0314' -- COMBINING REVERSED COMMA ABOVE
toChar (inr circumflex) = '\x0342' -- COMBINING GREEK PERISPOMENI
toChar (inr iotaSubscript) = '\x0345' -- COMBINING GREEK YPOGEGRAMMENI

proof : (x : Symbol ⊕ Mark) → defined x ≡ fromChar (toChar x)
proof (inl Α) = refl
proof (inl Β) = refl
proof (inl Γ) = refl
proof (inl Δ) = refl
proof (inl Ε) = refl
proof (inl Ζ) = refl
proof (inl Η) = refl
proof (inl Θ) = refl
proof (inl Ι) = refl
proof (inl Κ) = refl
proof (inl Λ) = refl
proof (inl Μ) = refl
proof (inl Ν) = refl
proof (inl Ξ) = refl
proof (inl Ο) = refl
proof (inl Π) = refl
proof (inl Ρ) = refl
proof (inl Σ′) = refl
proof (inl Τ) = refl
proof (inl Υ) = refl
proof (inl Φ) = refl
proof (inl Χ) = refl
proof (inl Ψ) = refl
proof (inl Ω) = refl
proof (inl α) = refl
proof (inl β) = refl
proof (inl γ) = refl
proof (inl δ) = refl
proof (inl ε) = refl
proof (inl ζ) = refl
proof (inl η) = refl
proof (inl θ) = refl
proof (inl ι) = refl
proof (inl κ) = refl
proof (inl ƛ) = refl
proof (inl μ) = refl
proof (inl ν) = refl
proof (inl ξ) = refl
proof (inl ο) = refl
proof (inl π) = refl
proof (inl ρ) = refl
proof (inl σ) = refl
proof (inl ς) = refl
proof (inl τ) = refl
proof (inl υ) = refl
proof (inl φ) = refl
proof (inl χ) = refl
proof (inl ψ) = refl
proof (inl ω) = refl
proof (inr acute) = refl
proof (inr grave) = refl
proof (inr circumflex) = refl
proof (inr smooth) = refl
proof (inr rough) = refl
proof (inr diaeresis) = refl
proof (inr iotaSubscript) = refl

Char↻Symbol⊕Mark : Char ↻ Symbol ⊕ Mark // NonGreekChar
Char↻Symbol⊕Mark = roundTripPartial fromChar toChar proof
