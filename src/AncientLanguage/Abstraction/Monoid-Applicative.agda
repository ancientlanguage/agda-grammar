module AncientLanguage.Abstraction.Monoid-Applicative where

open import AncientLanguage.Abstraction.Applicative
open import AncientLanguage.Abstraction.Monoid

module Monoid-Applicative {A : Set} (X : Monoid A) where

  open import AncientLanguage.Abstraction.Product
  open Monoid X

  inl : Applicative (_+ A)
  inl = applicative pure _⊛_
    where
    pure : {B : Set} → B → B + A
    pure = CP.inl

    _⊛_ : {B1 B2 : Set} → ((B1 → B2) + A) → (B1 + A) → (B2 + A)
    CP.inl f ⊛ CP.inl x = CP.inl (f x)
    CP.inl _ ⊛ CP.inr x = CP.inr x
    CP.inr x ⊛ CP.inl _ = CP.inr x
    CP.inr x ⊛ CP.inr y = CP.inr (x • y)

  inr : Applicative (A +_)
  inr = applicative pure _⊛_
    where
    pure : {B : Set} → B → A + B
    pure = CP.inr

    _⊛_ : {B1 B2 : Set} → (A + (B1 → B2)) → (A + B1) → (A + B2)
    CP.inl x ⊛ CP.inl y = CP.inl (x • y)
    CP.inl x ⊛ CP.inr _ = CP.inl x
    CP.inr _ ⊛ CP.inl x = CP.inl x
    CP.inr f ⊛ CP.inr x = CP.inr (f x)

  fst : Applicative (_× A)
  fst = applicative pure _⊛_
    where
    pure : {B : Set} → B → B × A
    pure x = x , identity

    _⊛_ : {B1 B2 : Set} → ((B1 → B2) × A) → (B1 × A) → (B2 × A)
    (f , y1) ⊛ (x , y2) = f x , y1 • y2

  snd : Applicative (A ×_)
  snd = applicative pure _⊛_
    where
    pure : {B : Set} → B → A × B
    pure x = identity , x

    _⊛_ : {B1 B2 : Set} → (A × (B1 → B2)) → (A × B1) → (A × B2)
    (x1 , f) ⊛ (x2 , y) = x1 • x2 , f y
