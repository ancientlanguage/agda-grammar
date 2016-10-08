module AncientLanguage.Test where

open import Agda.Builtin.Bool
open import Agda.Builtin.Char
open import Agda.Builtin.String
open import AncientLanguage.Common
open import AncientLanguage.PrimarySource using (Source; Group)
open import AncientLanguage.PrimarySource.Raw
open import AncientLanguage.PrimarySource.Greek.Sblgnt
open import AncientLanguage.PrimarySource.Greek.Sblgnt.Matthew
open import AncientLanguage.Grammar.Greek.Script.Mark
open import AncientLanguage.Grammar.Greek.Script.Symbol
open import AncientLanguage.Grammar.Greek.Script.Unicode-Symbol as Unicode-Symbol

maybeCons : {A : Set} → Bool → A → List A → List A
maybeCons true x xs = x ∷ xs
maybeCons false _ xs = xs

filter : {A : Set} → (A → Bool) → List A → List A
filter f [] = []
filter f (x ∷ xs) = maybeCons (f x) x (filter f xs)

isBeta : Char → Bool
isBeta 'β' = true
isBeta _ = false

betas : String → List Char
betas t = filter isBeta (primStringToList t)

sourceBetas : Source -> List Char
sourceBetas x = List.joinMap betas (raw x)

betaCount = List.length (List.joinMap sourceBetas (Group.getSources sblgnt))

matthew-symbol : List Char + List (List (Symbol + Mark))
matthew-symbol = traverse Unicode-Symbol.fromString (raw matthew)
  where
  traverse = Traverse.travList (MonoidalApplicative.inrApp listAppendMonoid)

test-matthew : inr (raw matthew) ≡ Over.travInr (List.map Unicode-Symbol.toString) matthew-symbol
test-matthew = refl
