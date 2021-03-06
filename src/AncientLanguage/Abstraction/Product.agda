module AncientLanguage.Abstraction.Product where

data ⊥ : Set where
open import Agda.Builtin.Unit public

infixr 7 _×_
infixr 6 _,_
record _×_ (A B : Set) : Set where
  no-eta-equality
  constructor _,_
  field
    fst : A
    snd : B

module Coproduct where
  infixr 6 _+_
  data _+_ (A B : Set) : Set where
    inl : A → A + B
    inr : B → A + B

  inlSet : {A B : Set} → A + B → Set
  inlSet (inl _) = ⊤
  inlSet (inr _) = ⊥

  asInl : {A B : Set} → (x : A + B) → {p : inlSet x} → A
  asInl (inl x) {tt} = x
  asInl (inr x) {()}

  inrSet : {A B : Set} → A + B → Set
  inrSet (inl _) = ⊥
  inrSet (inr _) = ⊤

  asInr : {A B : Set} → (x : A + B) → {p : inrSet x} → B
  asInr (inl x) {()}
  asInr (inr x) {tt} = x
open Coproduct using (_+_) public
module Sum = Coproduct


Maybe : Set → Set
Maybe A = ⊤ + A

pattern none = Sum.inl tt
pattern some x = Sum.inr x
