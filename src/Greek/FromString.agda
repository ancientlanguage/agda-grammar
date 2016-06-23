module Greek.FromString where

open import Agda.Builtin.Char
open import Core
open import Greek.Script
open Sum
open Concrete

from-char : Char → Char ⊕ Script
from-char 'Α' = inj2 (letter Α)
from-char 'Β' = inj2 (letter Β)
from-char 'Γ' = inj2 (letter Γ)
from-char 'Δ' = inj2 (letter Δ)
from-char 'Ε' = inj2 (letter Ε)
from-char 'Ζ' = inj2 (letter Ζ)
from-char 'Η' = inj2 (letter Η)
from-char 'Θ' = inj2 (letter Θ)
from-char 'Ι' = inj2 (letter Ι)
from-char 'Κ' = inj2 (letter Κ)
from-char 'Λ' = inj2 (letter Λ)
from-char 'Μ' = inj2 (letter Μ)
from-char 'Ν' = inj2 (letter Ν)
from-char 'Ξ' = inj2 (letter Ξ)
from-char 'Ο' = inj2 (letter Ο)
from-char 'Π' = inj2 (letter Π)
from-char 'Ρ' = inj2 (letter Ρ)
from-char 'Σ' = inj2 (letter Σ)
from-char 'Τ' = inj2 (letter Τ)
from-char 'Υ' = inj2 (letter Υ)
from-char 'Φ' = inj2 (letter Φ)
from-char 'Χ' = inj2 (letter Χ)
from-char 'Ψ' = inj2 (letter Ψ)
from-char 'Ω' = inj2 (letter Ω)
from-char 'α' = inj2 (letter α)
from-char 'β' = inj2 (letter β)
from-char 'γ' = inj2 (letter γ)
from-char 'δ' = inj2 (letter δ)
from-char 'ε' = inj2 (letter ε)
from-char 'ζ' = inj2 (letter ζ)
from-char 'η' = inj2 (letter η)
from-char 'θ' = inj2 (letter θ)
from-char 'ι' = inj2 (letter ι)
from-char 'κ' = inj2 (letter κ)
from-char 'λ' = inj2 (letter ƛ)
from-char 'μ' = inj2 (letter μ)
from-char 'ν' = inj2 (letter ν)
from-char 'ξ' = inj2 (letter ξ)
from-char 'ο' = inj2 (letter ο)
from-char 'π' = inj2 (letter π)
from-char 'ρ' = inj2 (letter ρ)
from-char 'σ' = inj2 (letter σ)
from-char 'ς' = inj2 (letter ς)
from-char 'τ' = inj2 (letter τ)
from-char 'υ' = inj2 (letter υ)
from-char 'φ' = inj2 (letter φ)
from-char 'χ' = inj2 (letter χ)
from-char 'ψ' = inj2 (letter ψ)
from-char 'ω' = inj2 (letter ω)
from-char '\x0300' = inj2 (mark grave) -- COMBINING GRAVE ACCENT
from-char '\x0301' = inj2 (mark acute) -- COMBINING ACUTE ACCENT
from-char '\x0308' = inj2 (mark diaeresis) -- COMBINING DIAERESIS
from-char '\x0313' = inj2 (mark smooth) -- COMBINING COMMA ABOVE
from-char '\x0314' = inj2 (mark rough) -- COMBINING REVERSED COMMA ABOVE
from-char '\x0342' = inj2 (mark circumflex) -- COMBINING GREEK PERISPOMENI
from-char '\x0345' = inj2 (mark iota-sub) -- COMBINING GREEK YPOGEGRAMMENI
from-char '(' = inj2 (punctuation left-paren)
from-char ')' = inj2 (punctuation right-paren)
from-char ',' = inj2 (punctuation comma)
from-char '.' = inj2 (punctuation period)
from-char '·' = inj2 (punctuation mid-dot)
from-char '—' = inj2 (punctuation em-dash)
from-char ';' = inj2 (punctuation semicolon)
from-char x = inj1 x

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
open Sum.Assert
from-string : (xs : String) → {{_ : [ Which.inj2? (assert-inj2 (from-any-string xs)) ]}} → List Script
from-string xs {{p}} with assert-inj2 (from-any-string xs)
… | inj1 a = from-⊥ p
… | inj2 b = b

instance
  StringScript : IsString (List Script)
  IsString.Constraint StringScript xs = [ Which.inj2? (assert-inj2 (from-any-string xs)) ]
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
