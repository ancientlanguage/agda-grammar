module Common.FunctorLawsMaybe where

open import Agda.Primitive
open import Prelude.Functor
  using (Functor)
open import Prelude.Path
open import Prelude.Monoidal.Product.Indexed
open import Common.FunctorLaws

open Π

module FLMaybe where
  data  Maybe ..{ℓ} (A : Set ℓ) : Set ℓ where
    no : Maybe A
    so : (a : A) → Maybe A

  map
    : ∀ ..{ℓ₀ ℓ₁} {A : Set ℓ₀} {B : Set ℓ₁}
    → (A → B)
    → (Maybe A → Maybe B)
  map f no = no
  map f (so a) = so (f a)

  identity
    : {la : Level}
    → {A : Set la}
    → (ta : Maybe A)
    → map idn ta ≡ ta
  identity no = refl
  identity (so a) = refl

  composition
    : {la lb lc : Level}
    → {A : Set la}
    → {B : Set lb}
    → {C : Set lc}
    → (f : A → B)
    → (g : B → C)
    → (ta : Maybe A)
    → map (g ∘ f) ta ≡ (map g ∘ map f) ta
  composition f g no = refl
  composition f g (so a) = refl

  instance
    functor
      : ∀ ..{ℓ}
      → Functor (Maybe {ℓ = ℓ})
    Functor.map functor = map

  x : {la : Level} → FunctorLaws (Maybe {ℓ = la})
  x = functorLaws identity composition
