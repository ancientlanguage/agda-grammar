module AncientLanguage.Grammar.Greek.Script.GroupMarks where

open import AncientLanguage.Abstraction
open import AncientLanguage.Grammar.Greek.Script.Mark

data Error : Set where
  initial-marks : Fwd Mark → Error

to : {A : Set} → Fwd (A + Mark) → Fwd Error + Fwd (A × Fwd Mark)
to {A} xs with Fwd.foldr f ([] , []) xs
  where
  f : A + Mark → Fwd Mark × Fwd (A × Fwd Mark) → Fwd Mark × Fwd (A × Fwd Mark)
  f (Sum.inl x) (ms , xs) = [] , (x , ms :> xs)
  f (Sum.inr x) (ms , xs) = (x :> ms) , xs
to xs | [] , snd = Sum.inr snd
to xs | (x :> fst) , snd = Sum.inl (Fwd.singleton (initial-marks (x :> fst)))

from : {A : Set} → Fwd (A × Fwd Mark) → Fwd (A + Mark)
from [] = []
from (fst , snd :> xs) = (Sum.inl fst :> Fwd.map Sum.inr snd) Fwd.++ (from xs)

module Test where
  open import AncientLanguage.Grammar.Greek.Script.Letter
  value : Fwd (Letter + Mark)
  value = Sum.inl α :> Sum.inr acute :> []

  around : from (Sum.asInr (to value)) ≡ value
  around = refl

  invalid : Fwd (Letter + Mark)
  invalid = Sum.inr acute :> Sum.inl α :> []

  test-invalid : Fwd Error
  test-invalid = Sum.asInl (to invalid)
