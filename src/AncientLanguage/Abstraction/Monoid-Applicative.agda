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
    pure = Sum.inl

    _⊛_ : {B1 B2 : Set} → ((B1 → B2) + A) → (B1 + A) → (B2 + A)
    Sum.inl f ⊛ Sum.inl x = Sum.inl (f x)
    Sum.inl _ ⊛ Sum.inr x = Sum.inr x
    Sum.inr x ⊛ Sum.inl _ = Sum.inr x
    Sum.inr x ⊛ Sum.inr y = Sum.inr (x • y)

  inr : Applicative (A +_)
  inr = applicative pure _⊛_
    where
    pure : {B : Set} → B → A + B
    pure = Sum.inr

    _⊛_ : {B1 B2 : Set} → (A + (B1 → B2)) → (A + B1) → (A + B2)
    Sum.inl x ⊛ Sum.inl y = Sum.inl (x • y)
    Sum.inl x ⊛ Sum.inr _ = Sum.inl x
    Sum.inr _ ⊛ Sum.inl x = Sum.inl x
    Sum.inr f ⊛ Sum.inr x = Sum.inr (f x)

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
