module AncientLanguage.Test where

open import Agda.Builtin.Bool
open import Agda.Builtin.Char
open import Agda.Builtin.String
open import AncientLanguage.Common
open import AncientLanguage.PrimarySource using (Source; Group)
open import AncientLanguage.PrimarySource.Raw
open import AncientLanguage.PrimarySource.Greek.Sblgnt

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
sourceBetas x = joinMap betas (raw x)

betaCount = length (joinMap sourceBetas (Group.getSources sblgnt))

testBetaCount : betaCount ≡ 3356
testBetaCount = refl
