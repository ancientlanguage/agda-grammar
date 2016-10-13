module AncientLanguage.Grammar.Greek.Script.Unicode-Symbol where

open import Agda.Builtin.Char
open import Agda.Builtin.String
open import AncientLanguage.Abstraction
open import AncientLanguage.Grammar.Greek.Script.Mark
open import AncientLanguage.Grammar.Greek.Script.Symbol

pattern valid-symbol x = CP.inr (CP.inl x)
pattern valid-mark x = CP.inr (CP.inr x)
pattern invalid-char x = CP.inl x

to : Char → Char + (Symbol + Mark)
to 'Α' = valid-symbol Α
to 'Β' = valid-symbol Β
to 'Γ' = valid-symbol Γ
to 'Δ' = valid-symbol Δ
to 'Ε' = valid-symbol Ε
to 'Ζ' = valid-symbol Ζ
to 'Η' = valid-symbol Η
to 'Θ' = valid-symbol Θ
to 'Ι' = valid-symbol Ι
to 'Κ' = valid-symbol Κ
to 'Λ' = valid-symbol Λ
to 'Μ' = valid-symbol Μ
to 'Ν' = valid-symbol Ν
to 'Ξ' = valid-symbol Ξ
to 'Ο' = valid-symbol Ο
to 'Π' = valid-symbol Π
to 'Ρ' = valid-symbol Ρ
to 'Σ' = valid-symbol Σ
to 'Τ' = valid-symbol Τ
to 'Υ' = valid-symbol Υ
to 'Φ' = valid-symbol Φ
to 'Χ' = valid-symbol Χ
to 'Ψ' = valid-symbol Ψ
to 'Ω' = valid-symbol Ω
to 'α' = valid-symbol α
to 'β' = valid-symbol β
to 'γ' = valid-symbol γ
to 'δ' = valid-symbol δ
to 'ε' = valid-symbol ε
to 'ζ' = valid-symbol ζ
to 'η' = valid-symbol η
to 'θ' = valid-symbol θ
to 'ι' = valid-symbol ι
to 'κ' = valid-symbol κ
to 'λ' = valid-symbol ƛ
to 'μ' = valid-symbol μ
to 'ν' = valid-symbol ν
to 'ξ' = valid-symbol ξ
to 'ο' = valid-symbol ο
to 'π' = valid-symbol π
to 'ρ' = valid-symbol ρ
to 'σ' = valid-symbol σ
to 'ς' = valid-symbol ς
to 'τ' = valid-symbol τ
to 'υ' = valid-symbol υ
to 'φ' = valid-symbol φ
to 'χ' = valid-symbol χ
to 'ψ' = valid-symbol ψ
to 'ω' = valid-symbol ω
to '\x0300' = valid-mark grave -- COMBINING GRAVE ACCENT
to '\x0301' = valid-mark acute -- COMBINING ACUTE ACCENT
to '\x0308' = valid-mark diaeresis -- COMBINING DIAERESIS
to '\x0313' = valid-mark smooth -- COMBINING COMMA ABOVE
to '\x0314' = valid-mark rough -- COMBINING REVERSED COMMA ABOVE
to '\x0342' = valid-mark circumflex -- COMBINING GREEK PERISPOMENI
to '\x0345' = valid-mark iota-sub -- COMBINING GREEK YPOGEGRAMMENI
to '\x2019' = valid-mark right-quote
to x = invalid-char x


pattern symbol x = CP.inl x
pattern mark x = CP.inr x

from : Symbol + Mark → Char
from (symbol Α) = 'Α'
from (symbol Β) = 'Β'
from (symbol Γ) = 'Γ'
from (symbol Δ) = 'Δ'
from (symbol Ε) = 'Ε'
from (symbol Ζ) = 'Ζ'
from (symbol Η) = 'Η'
from (symbol Θ) = 'Θ'
from (symbol Ι) = 'Ι'
from (symbol Κ) = 'Κ'
from (symbol Λ) = 'Λ'
from (symbol Μ) = 'Μ'
from (symbol Ν) = 'Ν'
from (symbol Ξ) = 'Ξ'
from (symbol Ο) = 'Ο'
from (symbol Π) = 'Π'
from (symbol Ρ) = 'Ρ'
from (symbol Σ) = 'Σ'
from (symbol Τ) = 'Τ'
from (symbol Υ) = 'Υ'
from (symbol Φ) = 'Φ'
from (symbol Χ) = 'Χ'
from (symbol Ψ) = 'Ψ'
from (symbol Ω) = 'Ω'
from (symbol α) = 'α'
from (symbol β) = 'β'
from (symbol γ) = 'γ'
from (symbol δ) = 'δ'
from (symbol ε) = 'ε'
from (symbol ζ) = 'ζ'
from (symbol η) = 'η'
from (symbol θ) = 'θ'
from (symbol ι) = 'ι'
from (symbol κ) = 'κ'
from (symbol ƛ) = 'λ'
from (symbol μ) = 'μ'
from (symbol ν) = 'ν'
from (symbol ξ) = 'ξ'
from (symbol ο) = 'ο'
from (symbol π) = 'π'
from (symbol ρ) = 'ρ'
from (symbol σ) = 'σ'
from (symbol ς) = 'ς'
from (symbol τ) = 'τ'
from (symbol υ) = 'υ'
from (symbol φ) = 'φ'
from (symbol χ) = 'χ'
from (symbol ψ) = 'ψ'
from (symbol ω) = 'ω'
from (mark grave) = '\x0300' -- COMBINING GRAVE ACCENT
from (mark acute) = '\x0301' -- COMBINING ACUTE ACCENT
from (mark diaeresis) = '\x0308' -- COMBINING DIAERESIS
from (mark smooth) = '\x0313' -- COMBINING COMMA ABOVE
from (mark rough) = '\x0314' -- COMBINING REVERSED COMMA ABOVE
from (mark circumflex) = '\x0342' -- COMBINING GREEK PERISPOMENI
from (mark iota-sub) = '\x0345' -- COMBINING GREEK YPOGEGRAMMENI
from (mark right-quote) = '\x2019'

stringToSymbol : String → Fwd Char + Fwd (Symbol + Mark)
stringToSymbol = TraverseInr.fwd asFwdChar ∘ primStringToList
  where
  asFwdChar = TraverseId.inl Fwd.singleton ∘ to

symbolToString : Fwd (Symbol + Mark) → String
symbolToString = primStringFromList ∘ Fwd.map from
