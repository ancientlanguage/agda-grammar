module AncientLanguage.Test where

open import Agda.Builtin.Bool
open import Agda.Builtin.Char
open import Agda.Builtin.String
open import AncientLanguage.Abstraction
open import AncientLanguage.PrimarySource using (Source; Group)
open import AncientLanguage.PrimarySource.Raw
open import AncientLanguage.PrimarySource.Greek.Sblgnt
open import AncientLanguage.PrimarySource.Greek.Sblgnt.Matthew
open import AncientLanguage.Grammar.Greek.Script.Mark
open import AncientLanguage.Grammar.Greek.Script.Symbol
open import AncientLanguage.Grammar.Greek.Script.Unicode-Symbol as Unicode-Symbol

maybeCons : {A : Set} → Bool → A → Fwd A → Fwd A
maybeCons true x xs = x :> xs
maybeCons false _ xs = xs

filter : {A : Set} → (A → Bool) → Fwd A → Fwd A
filter f [] = []
filter f (x :> xs) = maybeCons (f x) x (filter f xs)

isBeta : Char → Bool
isBeta 'β' = true
isBeta _ = false

betas : String → Fwd Char
betas t = filter isBeta (primStringToList t)

sourceBetas : Source -> Fwd Char
sourceBetas x = Fwd.joinMap betas (raw x)

betaCount = Fwd.length (Fwd.joinMap sourceBetas (Group.getSources sblgnt))

matthew-symbol : Fwd Char + Fwd (Fwd (Symbol + Mark))
matthew-symbol = TraverseInr.fwd Unicode-Symbol.fromString (raw matthew)

test-matthew : CP.inr (raw matthew) ≡ TraverseId.inr (Fwd.map Unicode-Symbol.toString) matthew-symbol
test-matthew = refl
