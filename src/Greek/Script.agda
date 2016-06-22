module Greek.Script where

module Concrete where
  data Letter : Set where
    Α Β Γ Δ Ε Ζ Η Θ Ι Κ Λ Μ Ν Ξ Ο Π Ρ Σ Τ Υ Φ Χ Ψ Ω α β γ δ ε ζ η θ ι κ ƛ μ ν ξ ο π ρ σ ς τ υ φ χ ψ ω : Letter

data Mark : Set where
  acute grave circumflex smooth rough diaeresis iota-sub : Mark

data Punctuation : Set where
  comma mid-dot semicolon period left-paren right-paren em-dash : Punctuation

data Script : Set where
  letter : Concrete.Letter → Script
  mark : Mark → Script
  punctuation : Punctuation → Script

module FromString where
  open import Agda.Builtin.Char
  open import Core
  open Coproduct
  open Concrete

  from-char : Char → Char + Script
  from-char 'Α' = |> letter Α
  from-char 'Β' = |> letter Β
  from-char 'Γ' = |> letter Γ
  from-char 'Δ' = |> letter Δ
  from-char 'Ε' = |> letter Ε
  from-char 'Ζ' = |> letter Ζ
  from-char 'Η' = |> letter Η
  from-char 'Θ' = |> letter Θ
  from-char 'Ι' = |> letter Ι
  from-char 'Κ' = |> letter Κ
  from-char 'Λ' = |> letter Λ
  from-char 'Μ' = |> letter Μ
  from-char 'Ν' = |> letter Ν
  from-char 'Ξ' = |> letter Ξ
  from-char 'Ο' = |> letter Ο
  from-char 'Π' = |> letter Π
  from-char 'Ρ' = |> letter Ρ
  from-char 'Σ' = |> letter Σ
  from-char 'Τ' = |> letter Τ
  from-char 'Υ' = |> letter Υ
  from-char 'Φ' = |> letter Φ
  from-char 'Χ' = |> letter Χ
  from-char 'Ψ' = |> letter Ψ
  from-char 'Ω' = |> letter Ω
  from-char 'α' = |> letter α
  from-char 'β' = |> letter β
  from-char 'γ' = |> letter γ
  from-char 'δ' = |> letter δ
  from-char 'ε' = |> letter ε
  from-char 'ζ' = |> letter ζ
  from-char 'η' = |> letter η
  from-char 'θ' = |> letter θ
  from-char 'ι' = |> letter ι
  from-char 'κ' = |> letter κ
  from-char 'λ' = |> letter ƛ
  from-char 'μ' = |> letter μ
  from-char 'ν' = |> letter ν
  from-char 'ξ' = |> letter ξ
  from-char 'ο' = |> letter ο
  from-char 'π' = |> letter π
  from-char 'ρ' = |> letter ρ
  from-char 'σ' = |> letter σ
  from-char 'ς' = |> letter ς
  from-char 'τ' = |> letter τ
  from-char 'υ' = |> letter υ
  from-char 'φ' = |> letter φ
  from-char 'χ' = |> letter χ
  from-char 'ψ' = |> letter ψ
  from-char 'ω' = |> letter ω
  from-char '\x0300' = |> mark grave -- COMBINING GRAVE ACCENT
  from-char '\x0301' = |> mark acute -- COMBINING ACUTE ACCENT
  from-char '\x0308' = |> mark diaeresis -- COMBINING DIAERESIS
  from-char '\x0313' = |> mark smooth -- COMBINING COMMA ABOVE
  from-char '\x0314' = |> mark rough -- COMBINING REVERSED COMMA ABOVE
  from-char '\x0342' = |> mark circumflex -- COMBINING GREEK PERISPOMENI
  from-char '\x0345' = |> mark iota-sub -- COMBINING GREEK YPOGEGRAMMENI
  from-char '(' = |> punctuation left-paren
  from-char ')' = |> punctuation right-paren
  from-char ',' = |> punctuation comma
  from-char '.' = |> punctuation period
  from-char '·' = |> punctuation mid-dot
  from-char '—' = |> punctuation em-dash
  from-char ';' = |> punctuation semicolon
  from-char x = x <|

  open import Agda.Primitive
  open import Agda.Builtin.List
  open import Agda.Builtin.String
  open import Unicode.Decompose
  map : {la lb : Level} {A : Set la} {B : Set lb} → (A → B) → List A → List B
  map f [] = []
  map f (x ∷ xs) = f x ∷ map f xs

  open import Agda.Builtin.Unit
  assume|> : {la lb : Level} {A : Set la} {B : Set lb} → List (A + B) → ⊤ + List B
  assume|> [] = |> []
  assume|> ((a <|) ∷ xs) = _ <|
  assume|> ((|> b) ∷ xs) with assume|> xs
  assume|> ((|> b) ∷ xs) | a <| = _ <|
  assume|> ((|> b) ∷ xs) | |> bs = |> b ∷ bs

  from-any-string : String → List (Char + Script)
  from-any-string xs = map from-char (primStringToList (decompose xs))

  open import Agda.Builtin.Bool
  open import Agda.Builtin.Unit
  open import Agda.Builtin.FromString
  open Inhabit
  from-string : (xs : String) → {{_ : [ Bool.is|> (assume|> (from-any-string xs)) ]}} → List Script
  from-string xs {{p}} with assume|> (from-any-string xs)
  … | a <| = from-⊥ p
  … | |> b = b

  instance
    StringScript : IsString (List Script)
    IsString.Constraint StringScript xs = [ Bool.is|> (assume|> (from-any-string xs)) ] 
    IsString.fromString StringScript xs = from-string xs

  module Sanity where
    open import Agda.Builtin.List
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
