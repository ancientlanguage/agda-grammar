module AncientLanguage.Abstraction.List where

open import Agda.Builtin.Nat

module Fwd where
  open import Agda.Builtin.List
    renaming (List to Fwd)
    using ([])
    renaming (_∷_ to _:>_)
    public

  length : {A : Set} → Fwd A → Nat
  length [] = 0
  length (_ :> xs) = suc (length xs)

  append : {A : Set} → (xs ys : Fwd A) → Fwd A
  append [] ys = ys
  append (x :> xs) ys = x :> append xs ys

  infixl 1 _++_
  _++_ = append

  join : {A : Set} → Fwd (Fwd A) → Fwd A
  join [] = []
  join (x :> xs) = append x (join xs)

  map : {A B : Set} → (f : A → B) → (xs : Fwd A) → Fwd B
  map f [] = []
  map f (x :> xs) = f x :> map f xs

  joinMap : {A B : Set} → (f : A → Fwd B) → (xs : Fwd A) → Fwd B
  joinMap f [] = []
  joinMap f (x :> xs) = append (f x) (joinMap f xs)

  singleton : {A : Set} → A → Fwd A
  singleton x = x :> []

  foldr : {A B : Set} → (A → B → B) → B → Fwd A → B
  foldr f b [] = b
  foldr f b (x :> xs) = f x (foldr f b xs)

open Fwd using (Fwd; []; _:>_) public
