module AncientLanguage.Grammar.Greek.Script.Unicode-Symbol where

open import Agda.Builtin.Char
open import Agda.Builtin.String
open import AncientLanguage.Common
open import AncientLanguage.Grammar.Greek.Script.Mark
open import AncientLanguage.Grammar.Greek.Script.Symbol

pattern valid-symbol x = inr (inl x)
pattern valid-mark x = inr (inr x)
pattern invalid-char x = inl x

from : Char → Char + (Symbol + Mark)
from 'Α' = valid-symbol Α
from 'Β' = valid-symbol Β
from 'Γ' = valid-symbol Γ
from 'Δ' = valid-symbol Δ
from 'Ε' = valid-symbol Ε
from 'Ζ' = valid-symbol Ζ
from 'Η' = valid-symbol Η
from 'Θ' = valid-symbol Θ
from 'Ι' = valid-symbol Ι
from 'Κ' = valid-symbol Κ
from 'Λ' = valid-symbol Λ
from 'Μ' = valid-symbol Μ
from 'Ν' = valid-symbol Ν
from 'Ξ' = valid-symbol Ξ
from 'Ο' = valid-symbol Ο
from 'Π' = valid-symbol Π
from 'Ρ' = valid-symbol Ρ
from 'Σ' = valid-symbol Σ
from 'Τ' = valid-symbol Τ
from 'Υ' = valid-symbol Υ
from 'Φ' = valid-symbol Φ
from 'Χ' = valid-symbol Χ
from 'Ψ' = valid-symbol Ψ
from 'Ω' = valid-symbol Ω
from 'α' = valid-symbol α
from 'β' = valid-symbol β
from 'γ' = valid-symbol γ
from 'δ' = valid-symbol δ
from 'ε' = valid-symbol ε
from 'ζ' = valid-symbol ζ
from 'η' = valid-symbol η
from 'θ' = valid-symbol θ
from 'ι' = valid-symbol ι
from 'κ' = valid-symbol κ
from 'λ' = valid-symbol ƛ
from 'μ' = valid-symbol μ
from 'ν' = valid-symbol ν
from 'ξ' = valid-symbol ξ
from 'ο' = valid-symbol ο
from 'π' = valid-symbol π
from 'ρ' = valid-symbol ρ
from 'σ' = valid-symbol σ
from 'ς' = valid-symbol ς
from 'τ' = valid-symbol τ
from 'υ' = valid-symbol υ
from 'φ' = valid-symbol φ
from 'χ' = valid-symbol χ
from 'ψ' = valid-symbol ψ
from 'ω' = valid-symbol ω
from '\x0300' = valid-mark grave -- COMBINING GRAVE ACCENT
from '\x0301' = valid-mark acute -- COMBINING ACUTE ACCENT
from '\x0308' = valid-mark diaeresis -- COMBINING DIAERESIS
from '\x0313' = valid-mark smooth -- COMBINING COMMA ABOVE
from '\x0314' = valid-mark rough -- COMBINING REVERSED COMMA ABOVE
from '\x0342' = valid-mark circumflex -- COMBINING GREEK PERISPOMENI
from '\x0345' = valid-mark iota-sub -- COMBINING GREEK YPOGEGRAMMENI
from '\x2019' = valid-mark right-quote
from x = invalid-char x


pattern symbol x = inl x
pattern mark x = inr x

to : Symbol + Mark → Char
to (symbol Α) = 'Α'
to (symbol Β) = 'Β'
to (symbol Γ) = 'Γ'
to (symbol Δ) = 'Δ'
to (symbol Ε) = 'Ε'
to (symbol Ζ) = 'Ζ'
to (symbol Η) = 'Η'
to (symbol Θ) = 'Θ'
to (symbol Ι) = 'Ι'
to (symbol Κ) = 'Κ'
to (symbol Λ) = 'Λ'
to (symbol Μ) = 'Μ'
to (symbol Ν) = 'Ν'
to (symbol Ξ) = 'Ξ'
to (symbol Ο) = 'Ο'
to (symbol Π) = 'Π'
to (symbol Ρ) = 'Ρ'
to (symbol Σ) = 'Σ'
to (symbol Τ) = 'Τ'
to (symbol Υ) = 'Υ'
to (symbol Φ) = 'Φ'
to (symbol Χ) = 'Χ'
to (symbol Ψ) = 'Ψ'
to (symbol Ω) = 'Ω'
to (symbol α) = 'α'
to (symbol β) = 'β'
to (symbol γ) = 'γ'
to (symbol δ) = 'δ'
to (symbol ε) = 'ε'
to (symbol ζ) = 'ζ'
to (symbol η) = 'η'
to (symbol θ) = 'θ'
to (symbol ι) = 'ι'
to (symbol κ) = 'κ'
to (symbol ƛ) = 'λ'
to (symbol μ) = 'μ'
to (symbol ν) = 'ν'
to (symbol ξ) = 'ξ'
to (symbol ο) = 'ο'
to (symbol π) = 'π'
to (symbol ρ) = 'ρ'
to (symbol σ) = 'σ'
to (symbol ς) = 'ς'
to (symbol τ) = 'τ'
to (symbol υ) = 'υ'
to (symbol φ) = 'φ'
to (symbol χ) = 'χ'
to (symbol ψ) = 'ψ'
to (symbol ω) = 'ω'
to (mark grave) = '\x0300' -- COMBINING GRAVE ACCENT
to (mark acute) = '\x0301' -- COMBINING ACUTE ACCENT
to (mark diaeresis) = '\x0308' -- COMBINING DIAERESIS
to (mark smooth) = '\x0313' -- COMBINING COMMA ABOVE
to (mark rough) = '\x0314' -- COMBINING REVERSED COMMA ABOVE
to (mark circumflex) = '\x0342' -- COMBINING GREEK PERISPOMENI
to (mark iota-sub) = '\x0345' -- COMBINING GREEK YPOGEGRAMMENI
to (mark right-quote) = '\x2019'

fromString : String → Fwd Char + Fwd (Symbol + Mark)
fromString = travFwd (Over.travInl Fwd.singleton ∘ from) ∘ primStringToList
  where
  open MonoidalApplicative fwdAppendMonoid
  open Traverse inrApp

toString : Fwd (Symbol + Mark) → String
toString = primStringFromList ∘ Fwd.map to
