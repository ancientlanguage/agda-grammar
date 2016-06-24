module Greek.FromString where

open import Agda.Builtin.Char
open import Core
open import Greek.Script
open Sum
open Concrete

from-char : Char → Char ⊕ Script
from-char 'Α' = inr (letter Α)
from-char 'Β' = inr (letter Β)
from-char 'Γ' = inr (letter Γ)
from-char 'Δ' = inr (letter Δ)
from-char 'Ε' = inr (letter Ε)
from-char 'Ζ' = inr (letter Ζ)
from-char 'Η' = inr (letter Η)
from-char 'Θ' = inr (letter Θ)
from-char 'Ι' = inr (letter Ι)
from-char 'Κ' = inr (letter Κ)
from-char 'Λ' = inr (letter Λ)
from-char 'Μ' = inr (letter Μ)
from-char 'Ν' = inr (letter Ν)
from-char 'Ξ' = inr (letter Ξ)
from-char 'Ο' = inr (letter Ο)
from-char 'Π' = inr (letter Π)
from-char 'Ρ' = inr (letter Ρ)
from-char 'Σ' = inr (letter Σ)
from-char 'Τ' = inr (letter Τ)
from-char 'Υ' = inr (letter Υ)
from-char 'Φ' = inr (letter Φ)
from-char 'Χ' = inr (letter Χ)
from-char 'Ψ' = inr (letter Ψ)
from-char 'Ω' = inr (letter Ω)
from-char 'α' = inr (letter α)
from-char 'β' = inr (letter β)
from-char 'γ' = inr (letter γ)
from-char 'δ' = inr (letter δ)
from-char 'ε' = inr (letter ε)
from-char 'ζ' = inr (letter ζ)
from-char 'η' = inr (letter η)
from-char 'θ' = inr (letter θ)
from-char 'ι' = inr (letter ι)
from-char 'κ' = inr (letter κ)
from-char 'λ' = inr (letter ƛ)
from-char 'μ' = inr (letter μ)
from-char 'ν' = inr (letter ν)
from-char 'ξ' = inr (letter ξ)
from-char 'ο' = inr (letter ο)
from-char 'π' = inr (letter π)
from-char 'ρ' = inr (letter ρ)
from-char 'σ' = inr (letter σ)
from-char 'ς' = inr (letter ς)
from-char 'τ' = inr (letter τ)
from-char 'υ' = inr (letter υ)
from-char 'φ' = inr (letter φ)
from-char 'χ' = inr (letter χ)
from-char 'ψ' = inr (letter ψ)
from-char 'ω' = inr (letter ω)
from-char '\x0300' = inr (mark grave) -- COMBINING GRAVE ACCENT
from-char '\x0301' = inr (mark acute) -- COMBINING ACUTE ACCENT
from-char '\x0308' = inr (mark diaeresis) -- COMBINING DIAERESIS
from-char '\x0313' = inr (mark smooth) -- COMBINING COMMA ABOVE
from-char '\x0314' = inr (mark rough) -- COMBINING REVERSED COMMA ABOVE
from-char '\x0342' = inr (mark circumflex) -- COMBINING GREEK PERISPOMENI
from-char '\x0345' = inr (mark iota-sub) -- COMBINING GREEK YPOGEGRAMMENI
from-char '(' = inr (punctuation left-paren)
from-char ')' = inr (punctuation right-paren)
from-char ',' = inr (punctuation comma)
from-char '.' = inr (punctuation period)
from-char '·' = inr (punctuation mid-dot)
from-char '—' = inr (punctuation em-dash)
from-char ';' = inr (punctuation semicolon)
from-char '\x2019' = inr (punctuation right-single-quote)
from-char x = inl x

open import Agda.Primitive
open import Agda.Builtin.List
open import Agda.Builtin.String
open import Unicode.Decompose
map : {la lb : Level} {A : Set la} {B : Set lb} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

from-any-string : String → List (Char ⊕ Script)
from-any-string xs = map from-char (primStringToList (decompose xs))

open import Agda.Builtin.Bool
open import Agda.Builtin.Unit
open import Agda.Builtin.FromString
open Inhabit
open List.Split
from-string : (xs : String) → {{p : inr?-set (split-inr (from-any-string xs))}} → List Script
from-string xs {{p}} = assert-inr (from-any-string xs) {p}

instance
  StringScript : IsString (List Script)
  IsString.Constraint StringScript xs = inr?-set (split-inr (from-any-string xs))
  IsString.fromString StringScript xs = from-string xs

module Sanity where
  open import Agda.Builtin.List
  concrete-letters : List Script
  concrete-letters = "ΑΒΓΔΕΖΗΘΙΚΛΜΝΞΟΠΡΣΤΥΦΧΨΩαβγδεζηθικλμνξοπρσςτυφχψ"
  check-punctuation : List Script
  check-punctuation = ",·;.()—"
  Βίβλος : List Script
  Βίβλος = "Βίβλος"
  Ἰησοῦ : List Script
  Ἰησοῦ = "Ἰησοῦ"
  Ἀβραάμ-period : List Script
  Ἀβραάμ-period = "Ἀβραάμ."
  Ἰσαάκ-comma : List Script
  Ἰσαάκ-comma = "Ἰσαάκ,"
  δὲ : List Script
  δὲ = "δὲ"
  left-paren-καὶ : List Script
  left-paren-καὶ = "(καὶ"
  Βροντῆς-right-paren-comma : List Script
  Βροντῆς-right-paren-comma = "Βροντῆς),"
  εἴκοσι-mid-dot : List Script
  εἴκοσι-mid-dot = "εἴκοσι)·"
  ἄγγελος-em-dash : List Script
  ἄγγελος-em-dash = "ἄγγελος—"
  μοι-semicolon : List Script
  μοι-semicolon = "μοι;"
  ἔδοξα : List Script
  ἔδοξα = "ἔδοξα"
  κατ’ : List Script
  κατ’ = "κατ’"
