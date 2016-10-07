module AncientLanguage.Common where

open import Agda.Primitive
open import Agda.Builtin.Equality public
open import Agda.Builtin.Nat using (Nat; zero; suc) public

import AncientLanguage.Common.List
module List = AncientLanguage.Common.List
open List using (List; []; _∷_) public

infixr 7 _×_
infixr 6 _+_
infixl 1 _∘_
infixr 1 _,_

data ⊥ : Set where
open import Agda.Builtin.Unit public

record _×_ (A B : Set) : Set where
  no-eta-equality
  constructor _,_
  field
    fst : A
    snd : B

data _+_ (A B : Set) : Set where
  inl : A → A + B
  inr : B → A + B

_∘_ : {A B C : Set} → (B → C) → (A → B) → A → C
(f ∘ g) x = f (g x)

const : {A B : Set} → B → (A → B)
const x _ = x

Maybe : Set → Set
Maybe A = ⊤ + A

pattern none = inl tt
pattern some x = inr x

record Monoid (A : Set) : Set where
  constructor monoid
  field
    identity : A
    _•_ : (x y : A) → A
  infixl 2 _•_

listAppendMonoid : {A : Set} → Monoid (List A)
listAppendMonoid = monoid [] List.append

record Applicative (F : Set → Set) : Set1 where
  constructor applicative
  field
    pure : {A : Set} → (x : A) → F A
    _⊛_ : {A B : Set} → (f : F (A → B)) → (x : F A) → F B
  infixl 2 _⊛_

id : {a : Level} → {A : Set a} → A → A
id x = x

idApp : Applicative id
idApp = applicative id id

module MonoidalApplicative {A : Set} (X : Monoid A) where
  open Monoid X

  inlApp : Applicative (_+ A)
  inlApp = applicative pure _⊛_
    where
    pure : {B : Set} → B → B + A
    pure = inl

    _⊛_ : {B1 B2 : Set} → ((B1 → B2) + A) → (B1 + A) → (B2 + A)
    inl f ⊛ inl x = inl (f x)
    inl _ ⊛ inr x = inr x
    inr x ⊛ inl _ = inr x
    inr x ⊛ inr y = inr (x • y)

  inrApp : Applicative (A +_)
  inrApp = applicative pure _⊛_
    where
    pure : {B : Set} → B → A + B
    pure = inr

    _⊛_ : {B1 B2 : Set} → (A + (B1 → B2)) → (A + B1) → (A + B2)
    inl x ⊛ inl y = inl (x • y)
    inl x ⊛ inr _ = inl x
    inr _ ⊛ inl x = inl x
    inr f ⊛ inr x = inr (f x)

  fstApp : Applicative (_× A)
  fstApp = applicative pure _⊛_
    where
    pure : {B : Set} → B → B × A
    pure x = x , identity

    _⊛_ : {B1 B2 : Set} → ((B1 → B2) × A) → (B1 × A) → (B2 × A)
    (f , y1) ⊛ (x , y2) = f x , y1 • y2

  sndApp : Applicative (A ×_)
  sndApp = applicative pure _⊛_
    where
    pure : {B : Set} → B → A × B
    pure x = identity , x

    _⊛_ : {B1 B2 : Set} → (A × (B1 → B2)) → (A × B1) → (A × B2)
    (x1 , f) ⊛ (x2 , y) = x1 • x2 , f y

Traversal : (F T : Set → Set) → Set1
Traversal F T = {A B : Set} → (A → F B) → T A → F (T B)

module Traverse {F : Set → Set} (X : Applicative F) where
  open Applicative X

  travList : Traversal F List
  travList f [] = pure []
  travList f (x ∷ xs) = pure _∷_ ⊛ f x ⊛ travList f xs

  travInl : {A : Set} → Traversal F (_+ A)
  travInl f (inl x) = pure inl ⊛ f x
  travInl f (inr x) = pure inr ⊛ pure x

  travInr : {A : Set} → Traversal F (A +_)
  travInr f (inl x) = pure inl ⊛ pure x
  travInr f (inr x) = pure inr ⊛ f x

  travFst : {A : Set} → Traversal F (_× A)
  travFst f (fst , snd) = pure _,_ ⊛ f fst ⊛ pure snd

  travSnd : {A : Set} → Traversal F (A ×_)
  travSnd f (fst , snd) = pure _,_ ⊛ pure fst ⊛ f snd

module Over = Traverse idApp
