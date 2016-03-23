module Common.RoundTripGeneralReflexive where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Prelude.Path
open import Common.Identity
open import Common.RoundTripGeneral

open ≡

roundTripGeneralReflexive :
  {F : {lf : Level} → Set lf → Set lf}
  {pure : {lx : Level} {X : Set lx} → X → F X}
  {liftDomain : {lx ly : Level} {X : Set lx} {Y : Set ly} → (X → F Y) → (F X → F Y)}
  {law : {lx ly : Level} {X : Set lx} {Y : Set ly} (f : X → F Y) (x : X) → liftDomain f (pure x) ≡ f x}
  {la : Level}
  {A : Set la}
  → RoundTripGeneral F pure liftDomain law A A
roundTripGeneralReflexive {pure = pure} {law = law} {A = A} = roundTripGeneral pure id p
  where
    p : (x : A) → pure x ≡ pure (id x)
    p x = pure · refl
