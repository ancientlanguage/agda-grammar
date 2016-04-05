module Common.FunctorLaws where

open import Agda.Primitive
open import Prelude.Functor
open import Prelude.Path
open import Prelude.Monoidal.Product.Indexed

open Π

record FunctorLaws
  ..{la lb : Level}
  (T : Set la → Set lb)
  ⦃ fun : Functor T ⦄
  : Set (lsuc la ⊔ lb) where
  constructor functorLaws
  field
    identity
      : {A : Set la}
      → (ta : T A)
      → Functor.map fun idn ta ≡ ta

    composition
      : ∀ {A B C}
      → (f : A → B)
      → (g : B → C)
      → (ta : T A)
      → Functor.map fun (g ∘ f) ta ≡ (Functor.map fun g ∘ Functor.map fun f) ta
