module AncientLanguage.Abstraction.Function where

open import Agda.Primitive

infixr 9 _∘_
_∘_ : {a b c : Level} → {A : Set a} → {B : Set b} → {C : Set c} → (B → C) → (A → B) → A → C
(f ∘ g) x = f (g x)

infixr 9 _∘ᵈ_
_∘ᵈ_
  : {a b c : Level}
  → {A : Set a}
  → {B : A → Set b}
  → {C : {x : A} → B x → Set c}
  → ({x : A} → (y : B x) → C y)
  → (g : (x : A) → B x)
  → (x : A)
  → C (g x)
(f ∘ᵈ g) x = f (g x)

infixr 0 _$_
_$_ : {a b : Level} → {A : Set a} → {B : Set b} → (A → B) → A → B
f $ x = f x

module Function where
  const : {A B : Set} → B → (A → B)
  const x _ = x

  id : {a : Level} → {A : Set a} → A → A
  id x = x
