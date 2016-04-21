module Common.RoundTrip.General.Definition where

open import Agda.Primitive
open import Agda.Builtin.Equality

record RoundTripGeneral
  (F : {lf : Level} → Set lf → Set lf)
  (pure : {lx : Level} {X : Set lx} → X → F X)
  (liftDomain : {lx ly : Level} {X : Set lx} {Y : Set ly} → (X → F Y) → (F X → F Y))
  (law : {lx ly : Level} {X : Set lx} {Y : Set ly} (f : X → F Y) (x : X) → liftDomain f (pure x) ≡ f x)
  {la lb : Level}
  (A : Set la)
  (B : Set lb)
  : Set (la ⊔ lb) where
  constructor roundTripGeneral
  field
    A→FB : A → F B
    B→A : B → A
    p : (x : B) → pure x ≡ A→FB (B→A x)
