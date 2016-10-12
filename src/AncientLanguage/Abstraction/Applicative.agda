module AncientLanguage.Abstraction.Applicative where

record Applicative (F : Set → Set) : Set1 where
  constructor applicative
  field
    pure : {A : Set} → (x : A) → F A
    _⊛_ : {A B : Set} → (f : F (A → B)) → (x : F A) → F B
  infixl 2 _⊛_
