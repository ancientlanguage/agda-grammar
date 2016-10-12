module AncientLanguage.Abstraction.Monoid where

record Monoid (A : Set) : Set where
  constructor monoid
  field
    identity : A
    _•_ : (x y : A) → A
  infixl 7 _•_
